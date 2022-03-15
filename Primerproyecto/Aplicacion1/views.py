from django.shortcuts import render, get_object_or_404
from django.http import JsonResponse
from django.template.loader import render_to_string 
from django.shortcuts import render
from .models import ConceptS, DescriptionS, Synonyms, ConceptosNoEncontrados, ExtendedmaprefsetS, SynonymVotes
from django.db.models import Q
from api.models import TokensDiagnosticos, TokensProcedures, Descripciones_y_sinonimos, TokensDiagnosticosYSinonimos
from .servicios import generarRequest, normalize, validateJSON
from nltk.tokenize import word_tokenize, sent_tokenize
from nltk.corpus import stopwords
import json
import copy
import nltk
import time
import es_core_news_lg
import spacy
from spacy import displacy
from negspacy.negation import Negex
import xlrd



from .negex import *
import csv
# Create your views here.


#--------funcion para acomodar tokens por valor de indiece con valor a 1 (largo de palabras de la descrpicion)
def Sort(sub_li): 
	sub_li.sort(key = lambda x: x[1],reverse=True)
	return sub_li

def Preprocesamiento(la_frase):
	nlp = spacy.load('es_core_news_lg')
	
	frase = la_frase
	document = nlp(frase)
	prev_prev_el = ""
	prev_el=""
	ele=""
	

	for index, token in enumerate(list(document)):
		print(token.lemma_, token.pos_, token.dep_)

	for index, token in enumerate(list(document)):
		if index+3 < len(list(document)):
			if (document[::][index].pos_ == "PROPN" or document[::][index].pos_ == "NOUN" or document[::][index].pos_ == "ADV") and document[::][index+1].pos_ == "ADJ" and document[::][index+2].pos_ == "CCONJ" and document[::][index+3].pos_ == "ADJ":
				noun = str(list(document)[::][index])
				adjective2 = str(list(document)[::][index+3])
				frase_nueva = noun +" "+ adjective2
				indice_frase_ori = frase.find(str(list(document)[::][index+3]))
				frase = frase.replace(str(list(document)[::][index+3]),frase_nueva)
				break
			if (document[::][index].pos_ == "PROPN" or document[::][index].pos_ == "NOUN" or document[::][index].pos_ == "ADV") and document[::][index+1].pos_ == "ADJ" and document[::][index+2].lemma_ == "," and document[::][index+3].pos_ == "ADJ":
				noun = str(list(document)[::][index])
				adjective2 = str(list(document)[::][index+3])
				frase_nueva = noun +" "+ adjective2
				indice_frase_ori = frase.find(str(list(document)[::][index+3]))
				frase = frase.replace(str(list(document)[::][index+3]),frase_nueva)
				break
		if index == 0 or index == 1:
			continue
		

		if index+2 < len(list(document)):
			if document[::][index-2].pos_ == "ADJ" and document[::][index-1].pos_ == "ADP" and (document[::][index].pos_ == "NOUN" or document[::][index].pos_ == "PROPN") and document[::][index+1].pos_ == "CCONJ" and (document[::][index+2].pos_ == "NOUN" or document[::][index+2].pos_ == "PROPN"):
				adjective = str(list(document)[::][index-2])
				adposition = str(list(document)[::][index-1])
				frase_nueva = adjective+ " "+adposition + " "+ str(list(document)[::][index+2])

				indice_frase_original = frase.find(str(list(document)[::][index+2])) #encontrar indicie del segundo NOUN
	
				frase = frase.replace(str(list(document)[::][index+2]),frase_nueva)

			if document[::][index-2].pos_ == "ADJ" and document[::][index-1].pos_ == "ADP" and (document[::][index].pos_ == "NOUN" or document[::][index].pos_ == "PROPN") and document[::][index+1].lemma_ == "," and (document[::][index+2].pos_ == "NOUN" or document[::][index+2].pos_ == "PROPN"):
				
				adjective = str(list(document)[::][index-2])
				adposition = str(list(document)[::][index-1])
				frase_nueva = adjective+ " "+adposition + " "+ str(list(document)[::][index+2])
	
				indice_frase_original = frase.find(str(list(document)[::][index+2])) #encontrar indicie del segundo NOUN
		
				frase = frase.replace(str(list(document)[::][index+2]),frase_nueva)



	return frase

#funicon para probar el procesamiento de distintos recursos de FHIR sin modificar la api
def InicioView(request):
	#pacientes = Paciente.objects.all()
	#recurso = 'PruebaPOS'
	#recurso = 'TokensDiagnosticos'
	recurso = 'nueva_tabla'
	#recurso = 'nueva_tabla_sinonimos'

	if (recurso == 'nueva_tabla_sinonimos'):
		start_time = time.time()

		syn = SynonymVotes.objects.filter(level = "2") and SynonymVotes.objects.filter(like = 1)#level 2 y like 1
		for sin in syn:
			des_sin = Synonyms.objects.get(id = int(sin.synonym_id))
			concepto_a_checar = ConceptS.objects.get(id = int(des_sin.conceptid))
			if concepto_a_checar.category_id == 6:				
				obj, created = Descripciones_y_sinonimos.objects.update_or_create(
	                    id = des_sin.id,
	                    conceptid=des_sin.conceptid,
	                    typeid= "900000000000013009",
	                    term=des_sin.term
	                    )
		print("---Creacion de tabla Descripciones y sinonimos con sinonimos %s seconds ---" % (time.time() - start_time))

			

		print("estoy en nueva tabla sinonimos")

	if (recurso == 'nueva_tabla'):
		start_time = time.time()
		concepto1 = ConceptS.objects.filter(active ="1") and ConceptS.objects.filter(category_id ="6")
		print("concepto1.coun", concepto1.count())

		for i in concepto1[0:0]:#115484
									desc = DescriptionS.objects.filter(conceptid = i.id, active="1")
									for j in desc:
										obj, created = Descripciones_y_sinonimos.objects.update_or_create(
						                        id = j.id,
						                        conceptid=j.conceptid,
						                        typeid=j.typeid,
						                        term=j.term
						                        )

		for row in Descripciones_y_sinonimos.objects.all().reverse():
			if Descripciones_y_sinonimos.objects.filter(conceptid=row.conceptid, typeid=row.typeid, term=row.term).count() > 1:
				row.delete()

		print("---Creacion de tabla Descripciones y sinonimos %s seconds ---" % (time.time() - start_time))

			

		


	if recurso == "conversion":#convertir los datos de notas clinicas en recursos bundle
		
		# path del archivo
		loc = ("C:/Users/artur/Django/env/Primerproyecto/Evolucion.xls")
		 
		# abrir workbook
		wb = xlrd.open_workbook(loc)
		sheet = wb.sheet_by_index(0)
		 
		# ejemplo row 0 y col 0
		print(sheet.cell_value(0, 0))
		print(type(sheet.cell_value(0, 0)))

		# numero de rows
		print("sheet.nrows", sheet.nrows)
		num_filas = sheet.nrows
		notas_de_evolucion = []
		dict_evolucion = {
		    "resourceType": "Bundle",
		    "entry": [
		        {
		            "fullUrl": "DiagnosticReport/D001",
		            "resource": {
		                      "resourceType" : "DiagnosticReport",
		                      "subject" : { "reference" : "Patient/P001" },
		                      "identifier" : [{ 
		                            "use" : "oficial",
		                            "value" : "D001"
		                             }],
		                      "conclusion" : ""
		                    }
		        }
		    ]
		}
		dict_of_dict ={}

		for i in range(1,num_filas):
			notas_de_evolucion.append(sheet.cell_value(i, 1))
			if i == 1:
				dict_evolucion = {
								    "resourceType": "Bundle",
								    "entry": [
								        {
								            "fullUrl": "DiagnosticReport/D"+str(i),
								            "resource": {
								                      "resourceType" : "DiagnosticReport",
								                      "subject" : { "reference" : "Patient/P"+str(i) },
								                      "identifier" : [{ 
								                            "use" : "oficial",
								                            "value" : "D"+str(i)
								                             }],
								                      "conclusion" : ""+(sheet.cell_value(i, 1).replace("\n",""))
								                    }
								        }
								    ]
								}
			else:
				new_entry = {
					            "fullUrl": "DiagnosticReport/D"+str(i),
					            "resource": {
					                      "resourceType" : "DiagnosticReport",
					                      "subject" : { "reference" : "Patient/P"+str(i) },
					                      "identifier" : [{ 
					                            "use" : "oficial",
					                            "value" : "D"+str(i)
					                             }],
					                      "conclusion" : ""+(sheet.cell_value(i, 1).replace("\n",""))
					                    }
					        }


				dict_evolucion['entry'].append(new_entry)
		"""with open('data.json', 'w', encoding="utf-8") as file:
									str(dict_evolucion).encode('utf-8')
									json.dump(dict_evolucion, file, indent=4, ensure_ascii=False)"""


		print("dict_evolucion", dict_evolucion)

		print("notas_de_evolucion", notas_de_evolucion)
		print("len(notas_de_evolucion)", len(notas_de_evolucion))

		"""
		{
		    "resourceType": "Bundle",
		    "entry": [
		        {
		            "fullUrl": "DiagnosticReport/D001",
		            "resource": {
		                      "resourceType" : "DiagnosticReport",
		                      "subject" : { "reference" : "Patient/P001" },
		                      "identifier" : [{ 
		                            "use" : "oficial",
		                            "value" : "D002"
		                             }],
		                      "conclusion" : "Paciente el cual lo encontramos en posicion semiflower, con carraspera."
		                    }
		        }
		    ]
		}
		"""


	if (recurso == 'PruebaPOS'):
		with open("TextoLibreAdministracion.json", "r") as read_file:
			try:
				responseMA = json.load(read_file)
				responseMA1 = copy.deepcopy(responseMA)
				#print("valido")
				isValid = True
			except ValueError as err:
				#print("invalido")
				isValid = False
		if isValid:
			stop_words = set(stopwords.words("spanish"))
			start_time = time.time()
			nlp = spacy.load('es_core_news_lg')
			#frase = "El paciente está orientado en tiempo y lugar"
			#frase = "El paciente está orientado en tiempo, dimension, espacio y lugar"
			#frase = "Abdomen depresible y doloroso"
			frase = "abdomen depresible, doloroso y distendido"
			frase2 = ""

			while(frase != frase2):
				if frase2 == "":					
					print("frase inicial: ", frase)
					frase2 = Preprocesamiento(frase)
					print("frase2", frase2)
					print("--- %s seconds ---" % (time.time() - start_time))
				else:
					frase = copy.deepcopy(frase2)
					frase2 = Preprocesamiento(frase)

			print("la frase final es :", frase2)


			data = "doc"

		else:
			responseMA ={"status": "json invalido"}
			responseMA1 = copy.deepcopy(responseMA)
			data=""



	if (recurso == 'TokensDiagnosticos'):
		with open("TextoLibreAdministracion.json", "r") as read_file:
			try:
				responseMA = json.load(read_file)
				responseMA1 = copy.deepcopy(responseMA)
				#print("valido")
				isValid = True
			except ValueError as err:
				#print("invalido")
				isValid = False
		if isValid:
			stop_words = set(stopwords.words("spanish"))
			descripciones = DescriptionS.objects.filter(category_id = 6)
			descAceptadas =[]

			start_time = time.time()
			concepto1 = ConceptS.objects.filter(active ="1") and ConceptS.objects.filter(category_id ="6")
			print("concepto1.coun", concepto1.count())

			"""for i in concepto1[0:0]:#115484
													desc = DescriptionS.objects.filter(conceptid = i.id)
													for j in desc:
														#print(j.term)
														tokens = [t for t in j.term.split()]
														#tokens = word_tokenize(j.term)
														filt_tokens = [w.lower() for w in tokens if not w.lower() in stop_words]
														for k in filt_tokens:
															TokensDiagnosticos.objects.create(token=k.lower(), id_descripcion=j.id, largo_palabras_termino=len(filt_tokens))
															descAceptadas.append([k.lower(), j.id, len(filt_tokens)])"""

			for i in concepto1[0:0]:#115484
				desc = Descripciones_y_sinonimos.objects.filter(conceptid = i.id)
				for j in desc:
					#print(j.term)
					tokens = [t for t in j.term.split()]
					#tokens = word_tokenize(j.term)
					filt_tokens = [w.lower() for w in tokens if not w.lower() in stop_words]
					for k in filt_tokens:
						TokensDiagnosticosYSinonimos.objects.create(token=k.lower(), id_descripcion=j.id, largo_palabras_termino=len(filt_tokens))
						descAceptadas.append([k.lower(), j.id, len(filt_tokens)])

			#for j in range(1):
				#for i in descripciones[j*5000:(j+1)*5000-1]:
					#concepto = ConceptS.objects.get(id = i.conceptid)
					#if concepto.active == "1":
						#descAceptadas.append(i)
			print("len-descAceptadas", len(descAceptadas))
			#print("descAceptadas", descAceptadas)
			print("--- %s seconds ---" % (time.time() - start_time))

			data = "doc"

		else:
			responseMA ={"status": "json invalido"}
			responseMA1 = copy.deepcopy(responseMA)
			data=""
	return render(request, 'Aplicacion1/index.html')


