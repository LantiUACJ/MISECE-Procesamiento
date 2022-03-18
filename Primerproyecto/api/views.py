from rest_framework.decorators import api_view
from rest_framework.response import Response
from django.shortcuts import render, get_object_or_404
from django.http import JsonResponse
from django.template.loader import render_to_string 
from django.shortcuts import render
from rest_framework import status    
from Aplicacion1.models import ConceptS, DescriptionS, Synonyms, ConceptosNoEncontrados
from django.db.models import Q
from Aplicacion1.servicios import generarRequest, normalize, validateJSON
import json
import copy
from api.models import TokensDiagnosticos, TokensDiagnosticosFrecuentes, TokensProcedures, Descripciones_y_sinonimos, TokensDiagnosticosYSinonimos
from Aplicacion1.servicios import generarRequest, normalize, validateJSON
from nltk.tokenize import word_tokenize, sent_tokenize
from nltk.corpus import stopwords
import nltk
import time
import es_core_news_lg
import numpy
import spacy
import threading
from django.db import connections
from joblib import Parallel, delayed
import multiprocessing
from functools import partial
from itertools import repeat
from multiprocessing import Pool, freeze_support

def Sort_0(sub_li): 
	sub_li.sort(key = lambda x: int(x[0]),reverse=False)
	return sub_li

def Sort(sub_li): 
	sub_li.sort(key = lambda x: x[1],reverse=True)
	return sub_li

def Sort_4(sub_li): 
	sub_li.sort(key = lambda x: x[4],reverse=True)
	return sub_li

def match_con_frase(frase_original, lista_conceptos_encontrados):
	l = lista_conceptos_encontrados
	frase_original = frase_original.lower()
	for i in l:
		if " (hallazgo)" in i["text"]:
			i["text"]= i["text"].replace(" (hallazgo)", "")
		elif " (trastorno)" in i["text"]:
			i["text"]= i["text"].replace(" (trastorno)", "")
		words = i["text"].split()
		buscar = words[-1]+" "
		if frase_original.rfind((words[-1]+" ").lower()) != -1:
			frase_original = frase_original.replace((words[-1]+" ").lower(), (("→"+words[-1]+" ")).lower())
			indice_final_frase = frase_original.rfind((words[-1]+" ").lower())+len(words[-1])
			frase_original = frase_original[:indice_final_frase] + "<<"+i["id"]+">>" +frase_original[indice_final_frase:]
		elif frase_original.rfind((words[-1]+",").lower()) != -1:
			frase_original = frase_original.replace((words[-1]+",").lower(), (("→"+words[-1]+",")).lower())
			indice_final_frase = frase_original.rfind((words[-1]+",").lower())+len(words[-1])
			frase_original = frase_original[:indice_final_frase] + "<<"+i["id"]+">>" +frase_original[indice_final_frase:]
		elif frase_original.rfind((words[-1]+".").lower()) != -1:
			frase_original = frase_original.replace((words[-1]+".").lower(), (("→"+words[-1]+".")).lower())
			indice_final_frase = frase_original.rfind((words[-1]+".").lower())+len(words[-1])
			frase_original = frase_original[:indice_final_frase] + "<<"+i["id"]+">>" +frase_original[indice_final_frase:]
		elif frase_original.rfind((words[-1]+")").lower()) != -1:
			frase_original = frase_original.replace((words[-1]+")").lower(), (("→"+words[-1]+")")).lower())
			indice_final_frase = frase_original.rfind((words[-1]+")").lower())+len(words[-1])
			frase_original = frase_original[:indice_final_frase] + "<<"+i["id"]+">>" +frase_original[indice_final_frase:]
		
	frase_con_ids = frase_original
	return frase_con_ids

def Preprocesamiento(indx, la_frase):
	nlp = spacy.load('es_core_news_lg')
	frase = la_frase
	document = nlp(frase)
	prev_prev_el = ""
	prev_el=""
	ele=""
	contador = 0
	frase2=""
	while frase != frase2:
		if frase != frase2:		
			frase2 = copy.deepcopy(frase)
			document = nlp(frase2)
			for index, token in enumerate(list(document)):
				#-------- Tipo postponer-----------
				if index+3 < len(list(document)):
					if (document[::][index].pos_ == "PROPN" or document[::][index].pos_ == "NOUN" or document[::][index].pos_ == "ADV" or document[::][index].pos_ == "PRON" ) and document[::][index+1].pos_ == "ADJ" and document[::][index+2].pos_ == "CCONJ" and document[::][index+3].pos_ == "ADJ":
						
						noun = str(list(document)[::][index])
						adjective2 = str(list(document)[::][index+3])
						frase_nueva = noun +" "+ adjective2
						indice_frase_ori = frase.find(str(list(document)[::][index+3]))
						frase = frase.replace(str(list(document)[::][index+3]),frase_nueva)
						
					if (document[::][index].pos_ == "PROPN" or document[::][index].pos_ == "NOUN" or document[::][index].pos_ == "ADV" or document[::][index].pos_ == "PRON" ) and document[::][index+1].pos_ == "ADJ" and document[::][index+2].lemma_ == "," and document[::][index+3].pos_ == "ADJ":
						noun = str(list(document)[::][index])
						adjective2 = str(list(document)[::][index+3])
						frase_nueva = noun +" "+ adjective2
						indice_frase_ori = frase.find(str(list(document)[::][index+3]))
						frase = frase.replace(str(list(document)[::][index+3]),frase_nueva)
										
				#------------------Tipo postponer con modificador (muy, mas y tan)
				if index+5 < len(list(document)):
					if (document[::][index].pos_ == "PROPN" or document[::][index].pos_ == "NOUN" or document[::][index].pos_ == "ADV" or document[::][index].pos_ == "PRON") and document[::][index+1].pos_ == "ADV" and document[::][index+2].pos_ == "ADJ" and document[::][index+3].pos_ == "CCONJ" and document[::][index+4].pos_ == "ADV" and document[::][index+5].pos_ == "ADJ":
						noun = str(list(document)[::][index])
						conjuncion= " "+ str(list(document)[::][index+3]) + " "
						adverb2 = str(list(document)[::][index+4])
						adjective2 = str(list(document)[::][index+5])
						frase_nueva = noun +" "+ adverb2 +" "+ adjective2
						indice_frase_ori = frase.find(conjuncion)
						frase = frase[:indice_frase_ori+3]+""+noun+" " +frase[indice_frase_ori+3:]
						#frase = frase.replace(str(list(document)[::][index+5]),frase_nueva)
						
					if (document[::][index].pos_ == "PROPN" or document[::][index].pos_ == "NOUN" or document[::][index].pos_ == "ADV" or document[::][index].pos_ == "PRON") and document[::][index+1].pos_ == "ADV" and document[::][index+2].pos_ == "ADJ" and document[::][index+3].pos_ == "PUNCT" and document[::][index+4].pos_ == "ADV" and document[::][index+5].pos_ == "ADJ":
						noun = str(list(document)[::][index])
						conjuncion= str(list(document)[::][index+3]) + " "
						adverb2 = str(list(document)[::][index+4])
						adjective2 = str(list(document)[::][index+5])
						frase_nueva = noun +" "+ adverb2 +" "+ adjective2
						indice_frase_ori = frase.find(conjuncion)
						
						frase = frase[:indice_frase_ori+2]+""+noun+" " +frase[indice_frase_ori+2:]
								
				#-------- Tipo anteponer entre preposicion-----------
				if index+2 < len(list(document)):
					if document[::][index-2].pos_ == "ADJ" and document[::][index-1].pos_ == "ADP" and (document[::][index].pos_ == "NOUN" or document[::][index].pos_ == "PROPN" or document[::][index].pos_ == "PRON") and document[::][index+1].pos_ == "CCONJ" and (document[::][index+2].pos_ == "NOUN" or document[::][index+2].pos_ == "PROPN"):
						adjective = str(list(document)[::][index-2])
						adposition = str(list(document)[::][index-1])
						frase_nueva = adjective+ " "+adposition + " "+ str(list(document)[::][index+2])
						indice_frase_original = frase.find(str(list(document)[::][index+2])) #encontrar indicie del segundo NOUN
						frase = frase.replace(str(list(document)[::][index+2]),frase_nueva)
					
					if document[::][index-2].pos_ == "ADJ" and document[::][index-1].pos_ == "ADP" and (document[::][index].pos_ == "NOUN" or document[::][index].pos_ == "PROPN" or document[::][index].pos_ == "PRON") and document[::][index+1].lemma_ == "," and (document[::][index+2].pos_ == "NOUN" or document[::][index+2].pos_ == "PROPN"):
						adjective = str(list(document)[::][index-2])
						adposition = str(list(document)[::][index-1])
						frase_nueva = adjective+ " "+adposition + " "+ str(list(document)[::][index+2])
			
						indice_frase_original = frase.find(str(list(document)[::][index+2])) #encontrar indicie del segundo NOUN
				
						frase = frase.replace(str(list(document)[::][index+2]),frase_nueva)
			
		else:
			break
	return [indx, frase2]

def ProcesarOracion2(frasePrueba, indexP, val, start_time):
	# ---------TOKENIZAR POR PALABRAS LA FRASE A PROCESAR
	stop_words = set(stopwords.words("spanish"))
	tokens_palabras = word_tokenize(frasePrueba)#tokenizo por palabras la frase del texto libre
	#print("--- %s seconds etapa 1 ---" % (time.time() - start_time))
	# ---------ELIMINAR STOPWORDS Y SUJETO DE ORACION
	filt_frasePrueba = [w for w in tokens_palabras if not w in stop_words]# se quitan las stopwords de los tokens(palabras)
	#print("--- %s seconds etapa 2 ---" % (time.time() - start_time))

	# ---------GENERAR LISTA ANIDADA POR CADA TOKEN = [ID_DESCRIPCION, LARGO_PALABRAS]
	id_terminos_de_token=[]
	
	bd_tokens = TokensDiagnosticos.objects.raw("SELECT * FROM `api_tokensdiagnosticos` WHERE token IN %s", [tuple(filt_frasePrueba)])
	arfil = numpy.asarray(filt_frasePrueba)
	for indx, i in enumerate(arfil):#por cada token en la frase
		id_terminos_de_token.append([])
		for j in bd_tokens:#por cada token en la bd
			if j.token == i and j.largo_palabras_termino <=  len(filt_frasePrueba):#si token de frase esta en token de la instancia de la bd
				#id_terminos_de_token[indx].append([j.id_descripcion, j.largo_palabras_termino, j.token])#añado id de la descripcion que continee el token de la frase
				id_terminos_de_token[indx].append([int(j.id_descripcion), j.largo_palabras_termino])#añado id de la descripcion que continee el token de la frase
	max=0
	#print("--- %s seconds etapa 3 ---" % (time.time() - start_time))

	# ---------ELIMINAR DESCRIPCIONES QUE TENGAN MAS PALABRAS QUE LA DE LA FRASE A PROCESAR, ORDENAR CADA LISTA ANIDADA DE CADA TOKEN DE LARGO DE PALABRAS EN DESCRIPCION DE MANERA DESCENDENTE
	for term in id_terminos_de_token:
		Sort(term)	   
	#print("--- %s seconds etapa 4 ---" % (time.time() - start_time))

	# ---------IDENTIFICACIÓN DE DESCRIPCIONES QUE CONTENGAN AL TOKEN CON LA MISMA LONGITUD QU ELA FRASE PROCESADA
	termino_correcto=[]
	
	ar = numpy.asarray(id_terminos_de_token)
	ar2 = copy.deepcopy(ar)
	cont = 0
	contador = 1
	contador2 = 0
	for term in ar:
		for tupla in term:
			longitud_termino = tupla[1]
			id_desc=tupla[0]
			cont=1
			for term2 in ar2[contador:]:
				for tupla2 in term2:
					if tupla2[0] == id_desc:
						cont=cont+1
			if cont == longitud_termino:
				if tupla not in termino_correcto:
					termino_correcto.append(tupla)
		if contador != ar.size:
			contador = contador + 1

	#print("--- %s seconds etapa 5 ---" % (time.time() - start_time))

	# ---------ELIMINAR REPETIDOS GENERADOS EN EL PROCESO INMEDIATO ANTERIOR
	termino_correct_sin_repetido=[]
	for term in termino_correcto:
		if term[0] not in termino_correct_sin_repetido:
			termino_correct_sin_repetido.append(term[0])
	#print("--- %s seconds etapa 6 ---" % (time.time() - start_time))

	# ---------EXTRAER CONCEPTOS DE ACUARDO A LAS DESCRIPCIONES
	conceptos = []
	for term in termino_correct_sin_repetido:
		desc = DescriptionS.objects.filter(id =int(term))
		conceptos.append([desc[0].conceptid, ])
	data=""
	#print("--- %s seconds etapa 7 ---" % (time.time() - start_time))

	#---------VERIFICACION SI EL ORDEN DE PALABRAS EN LA DESCRIPCION Y FRASE ESTA TAL CUAL DE MANERA VCONSECUTIVA
	BooleanTalCual =[]
	descSeguncon =[]
	for conc in conceptos:
		esta=0
		descripciones = Descripciones_y_sinonimos.objects.filter(conceptid = str(conc[0]))
		for descripcion in descripciones:
			if str(descripcion.term).lower() in str(frasePrueba).lower():
				esta=1
				indice_inicial = str(frasePrueba).lower().find(str(descripcion.term).lower())
				indice_final = indice_inicial + len(descripcion.term)
				descSeguncon.append([descripcion.term, conc[0], indice_inicial, indice_final, len(descripcion.term)])
		BooleanTalCual.append(esta)
	
	conceptos2 = []
	agregar=0
	for indexB, b in enumerate(BooleanTalCual):
		agregar = 0
		for indexC, c in enumerate(conceptos):
			if b == 1:
				agregar = 1
		if agregar == 1:
			conceptos2.append(conceptos[indexB])
	#print("--- %s seconds etapa 8 ---" % (time.time() - start_time))

	# ---------ELIMINAR CONCEPTOS QUE ESTAN CONTENIDO EN CONCEPTOS CON UNA DESCRIPCION MAYOR
	conceptos3=[]
	Sort_4(descSeguncon)

	for elitem1 in descSeguncon[::-1]:
		for elitem2 in descSeguncon[::-1]:
			if elitem1 != elitem2:
				if elitem2[2] >=  elitem1[2] and elitem2[2] <= elitem1[3] and elitem2[3] > elitem1[2] and elitem2[3] <= elitem1[3]:
					if elitem2 in descSeguncon:
						descSeguncon.remove(elitem2)

	for itemotro in descSeguncon:
		if itemotro[1] not in conceptos3:
			conceptos3.append(itemotro[1] )
	frasePrueba2=""

	aumento=0
	#print("--- %s seconds etapa 9 ---" % (time.time() - start_time))

	# ---------AÑADIR ENTRE GUIONES MEDIOS, LOS FSN DE LOS CONCEPTOS FINALES ENCONTRADOS
	conta = 0
	con_id=[]
	for indxconc3, conc3 in enumerate(conceptos3):
		descripciones = Descripciones_y_sinonimos.objects.filter(conceptid = str(conc3))
		for descripcion in descripciones:
			if str(descripcion.term).lower() in str(frasePrueba).lower():
				conta=conta+1
				if indxconc3 == 0:
					frasePrueba2 = copy.deepcopy(frasePrueba)
				indice_inicial = str(frasePrueba2).lower().find(str(descripcion.term).lower())
				indice_final = indice_inicial + len(descripcion.term)
				FSN = Descripciones_y_sinonimos.objects.get(conceptid = str(conc3), typeid = "900000000000003001")
				con_id.append([str(conc3), descripcion.term, FSN.term])
				frasePrueba2 = frasePrueba2[:(indice_final)] + ' <<'+FSN.id+'>>' + frasePrueba2[(indice_final):]
	#print("--- %s seconds etapa 10 ---" % (time.time() - start_time))

	# ---------AÑADIR PROPIEDAD "EXTENSION" AL JSON PARA MOSTRAR CUANTOS CONCEPTOS SE ENCONTRARON Y SU ID		
	if "fullUrl" in val:		
		if len(con_id) >= 1:
			for item in con_id:
				if "ConceptosSNOMED" not in val['resource']:
					val['resource'].update( {"ConceptosSNOMED": [{
					"url" : "codeSNOMEDActivo "+str(indexP),
					"id" : item[0],
					"text" : item[1],
					"FSN" : item[2]
					}]} )
				else:
					val['resource']["ConceptosSNOMED"].append( {
					"url" : "codeSNOMEDActivo "+str(indexP),
					"id" : item[0],
					"text" : item[1],
					"FSN" : item[2]
					} )
	else:
		if len(con_id) >= 1:
			for item in con_id:
				if "ConceptosSNOMED" not in val:
					val.update( {"ConceptosSNOMED": [{
					"url" : "codeSNOMEDActivo "+str(indexP),
					"id" : item[0],
					"text" : item[1],
					"FSN" : item[2]
					}]} )
				else:
					val["ConceptosSNOMED"].append( {
					"url" : "codeSNOMEDActivo "+str(indexP),
					"id" : item[0],
					"text" : item[1],
					"FSN" : item[2]
					} )
	#-----------Guardar tokens de los conceptos encontrados en la frase
	descAceptadas=[]
	for i in conceptos3:
		desc = Descripciones_y_sinonimos.objects.filter(conceptid = i)
		for j in desc:
			tokens = [t for t in j.term.split()]
			filt_tokens = [w.lower() for w in tokens if not w.lower() in stop_words]
			for k in filt_tokens:
				p, created = TokensDiagnosticosFrecuentes.objects.get_or_create(
			    token=k.lower(),
			    id_descripcion=j.id,
			    largo_palabras_termino=len(filt_tokens))
				descAceptadas.append([k.lower(), j.id, len(filt_tokens)])
	if frasePrueba2 == "":
		return [indexP, frasePrueba, 1]
	else:
		return [indexP, frasePrueba2, 1]
	
def ProcesarOracionFrecuentes(frasePrueba, indexP, val, start_time):
	# ---------TOKENIZAR POR PALABRAS LA FRASE A PROCESAR
	stop_words = set(stopwords.words("spanish"))
	tokens_palabras = word_tokenize(frasePrueba)#tokenizo por palabras la frase del texto libre
	# ---------ELIMINAR STOPWORDS Y SUJETOS (NSUBJ)
	filt_frasePrueba = [w for w in tokens_palabras if not w in stop_words]# se quitan las stopwords de los tokens(palabras)
	# ---------GENERAR LISTA ANIDADA POR CADA TOKEN = [ID_DESCRIPCION, LARGO_PALABRAS]
	id_terminos_de_token=[]
	bd_tokens = TokensDiagnosticosFrecuentes.objects.raw("SELECT * FROM `api_tokensdiagnosticosfrecuentes` WHERE token IN %s", [tuple(filt_frasePrueba)])
	
	arfil = numpy.asarray(filt_frasePrueba)
	for indx, i in enumerate(arfil):#por cada token en la frase
		id_terminos_de_token.append([])
		for j in bd_tokens:#por cada token en la bd
			if j.token == i and j.largo_palabras_termino <=  len(filt_frasePrueba):#si token de frase esta en token de la instancia de la bd
				id_terminos_de_token[indx].append([int(j.id_descripcion), j.largo_palabras_termino])#añado id de la descripcion que continee el token de la frase
	max=0
	#print("--- %s seconds etapa 3 bd frecuentes---" % (time.time() - start_time))
	# ---------ELIMINAR DESCRIPCIONES QUE TENGAN MAS PALABRAS QUE LA DE LA FRASE A PROCESAR, ORDENAR CADA LISTA ANIDADA DE CADA TOKEN DE LARGO DE PALABRAS EN DESCRIPCION DE MANERA DESCENDENTE
	for term in id_terminos_de_token:
		Sort(term)	   
	#print("--- %s seconds etapa 4 bd frecuentes---" % (time.time() - start_time))

	# ---------IDENTIFICACIÓN DE DESCRIPCIONES QUE CONTENGAN AL TOKEN CON LA MISMA LONGITUD QU ELA FRASE PROCESADA
	termino_correcto=[]
	
	ar = numpy.asarray(id_terminos_de_token)
	ar2 = copy.deepcopy(ar)
	
	contador = 1
	contador2 = 0
	cont=0
	for term in ar:
		for tupla in term:
			longitud_termino = tupla[1]
			id_desc=tupla[0]
			cont=1
			for term2 in ar2[contador:]:
				for tupla2 in term2:
					if tupla2[0] == id_desc:
						cont=cont+1
			if cont == longitud_termino:
				if tupla not in termino_correcto:
					termino_correcto.append(tupla)
		if contador != ar.size:
			contador = contador + 1
	#print("--- %s seconds etapa 5 bd frecuentes---" % (time.time() - start_time))

	# ---------ELIMINAR REPETIDOS GENERADOS EN EL PROCESO INMEDIATO ANTERIOR
	termino_correct_sin_repetido=[]
	for term in termino_correcto:
		if term[0] not in termino_correct_sin_repetido:
			termino_correct_sin_repetido.append(term[0])
	#print("--- %s seconds etapa 6 bd frecuentes ---" % (time.time() - start_time))

	# ---------EXTRAER CONCEPTOS DE ACUARDO A LAS DESCRIPCIONES
	conceptos = []
	for term in termino_correct_sin_repetido:
		desc = Descripciones_y_sinonimos.objects.filter(id =int(term))
		conceptos.append([desc[0].conceptid, ])
	data=""
	#print("--- %s seconds etapa 7 bd frecuentes---" % (time.time() - start_time))

	#---------VERIFICACION SI EL ORDEN DE PALABRAS EN LA DESCRIPCION Y FRASE ESTA TAL CUAL DE MANERA VCONSECUTIVA
	BooleanTalCual =[]
	descSeguncon =[]
	for conc in conceptos:
		esta=0
		descripciones = Descripciones_y_sinonimos.objects.filter(conceptid = str(conc[0]))
		for descripcion in descripciones:
			if str(descripcion.term).lower() in str(frasePrueba).lower():
				esta=1
				indice_inicial = str(frasePrueba).lower().find(str(descripcion.term).lower())
				indice_final = indice_inicial + len(descripcion.term)
				descSeguncon.append([descripcion.term, conc[0], indice_inicial, indice_final, len(descripcion.term)])
		BooleanTalCual.append(esta)
	
	conceptos2 = []
	agregar=0
	for indexB, b in enumerate(BooleanTalCual):
		agregar = 0
		for indexC, c in enumerate(conceptos):
			if b == 1:
				agregar = 1
		if agregar == 1:
			conceptos2.append(conceptos[indexB])
	#print("--- %s seconds etapa 8 bd frecuentes---" % (time.time() - start_time))
	# ---------ELIMINAR COCNEPCTOS QUE ESTAN CONTENIDO EN CONCEPTOS CON UNA DESCRIPCION MAYOR
	conceptos3=[]
	Sort_4(descSeguncon)

	for elitem1 in descSeguncon[::-1]:
		for elitem2 in descSeguncon[::-1]:
			if elitem1 != elitem2:
				if elitem2[2] >=  elitem1[2] and elitem2[2] <= elitem1[3] and elitem2[3] > elitem1[2] and elitem2[3] <= elitem1[3]:
					
					if elitem2 in descSeguncon:
						descSeguncon.remove(elitem2)

	for itemotro in descSeguncon:
		if itemotro[1] not in conceptos3:
			conceptos3.append(itemotro[1] )
	frasePrueba2=""

	aumento=0
	#print("--- %s seconds etapa 9 bd frecuentes---" % (time.time() - start_time))
	# ---------AÑADIR ENTRE GUIONES MEDIOS, LOS FSN DE LOS CONCEPTOS FINALES ENCONTRADOS
	conta = 0
	con_id=[]

	for indxconc3, conc3 in enumerate(conceptos3):
		descripciones = Descripciones_y_sinonimos.objects.filter(conceptid = str(conc3))
		for descripcion in descripciones:
			if str(descripcion.term).lower() in str(frasePrueba).lower():
				conta=conta+1
				if indxconc3 == 0:
					frasePrueba2 = copy.deepcopy(frasePrueba)
				indice_inicial = str(frasePrueba2).lower().find(str(descripcion.term).lower())
				indice_final = indice_inicial + len(descripcion.term)
				FSN = Descripciones_y_sinonimos.objects.get(conceptid = str(conc3), typeid = "900000000000003001")
				con_id.append([str(conc3), descripcion.term, FSN.term])
				frasePrueba2 = frasePrueba2[:(indice_final)] + ' <<'+FSN.conceptid+'>>' + frasePrueba2[(indice_final):]
	#print("--- %s seconds etapa 10 bd frecuentes---" % (time.time() - start_time))
	# ---------AÑADIR PROPIEDAD "EXTENSION" AL JSON PARA MOSTRAR CUANTOS CONCEPTOS SE ENCONTRARON Y SU ID		

	if "fullUrl" in val:		
		if len(con_id) >= 1:
			for item in con_id:
				if "ConceptosSNOMED" not in val['resource']:
					val['resource'].update( {"ConceptosSNOMED": [{
					"url" : "codeSNOMEDActivo "+str(indexP),
					"id" : item[0],
					"text" : item[1],
					"FSN" : item[2]
					}]} )
				else:
					val['resource']["ConceptosSNOMED"].append( {
					"url" : "codeSNOMEDActivo "+str(indexP),
					"id" : item[0],
					"text" : item[1],
					"FSN" : item[2]
					} )
	else:
		if len(con_id) >= 1:
			for item in con_id:
				if "ConceptosSNOMED" not in val:
					val.update( {"ConceptosSNOMED": [{
					"url" : "codeSNOMEDActivo "+str(indexP),
					"id" : item[0],
					"text" : item[1],
					"FSN" : item[2]
					}]} )
				else:
					val["ConceptosSNOMED"].append( {
					"url" : "codeSNOMEDActivo "+str(indexP),
					"id" : item[0],
					"text" : item[1],
					"FSN" : item[2]
					} )

	if frasePrueba2 == "":
		listaRetorno = [indexP, frasePrueba, 0]
	
	else:
		listaRetorno = [indexP, frasePrueba2, 1]
	return listaRetorno

@api_view(['GET'])
def apiOverview(request):
	api_urls = {
		'ProcesarSNOMED Bundle': '/procesarSNOMED/Bundle',
		'ProcesarSNOMED DiagnosticReport': '/procesarSNOMED/DiagnosticReport',
		'ProcesarSNOMED Medication': '/procesarSNOMED/Medication',
		'ProcesarSNOMED MedicationAdministration': '/procesarSNOMED/MedicationAdministration',
		'ProcesarSNOMED Procedure': '/procesarSNOMED/Procedure',
		'ProcesarSNOMED Observation': '/procesarSNOMED/Observation',

	}
	return Response(api_urls)

@api_view(['POST'])
def ProcesarBundleView(request):
	responseMA = request.data
	if (responseMA):
		recurso = responseMA['resourceType']
		
		if (recurso == 'Bundle'):
		 start_time = time.time()
		 responseMA = request.data
		 responseMA1 = copy.deepcopy(responseMA)
		 for val in responseMA['entry']:
		 	if "Medication" == val['resource']['resourceType']:
		 		if 'code' in val['resource']:
		 			if 'text' in val['resource']['code']:
		 				data = normalize(val['resource']['code']['text'])
				 		descripciones = DescriptionS.objects.filter(term = data) & DescriptionS.objects.filter(category_id = 10)
				 		sinonimos = Synonyms.objects.filter(term = data)
				 		if descripciones.count() > 1:
				 			for i in descripciones:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				descripciones = descripciones.exclude(id=i.id)
					 	if sinonimos.count() > 1:
				 			for i in sinonimos:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				sinonimos = sinonimos.exclude(id=i.id)
				 		if descripciones:
				 			concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
				 			if concepto.active == '1':
				 				val['resource'].update( {"extension": [{
				 					"url" : "codeSNOMEDActivo",
				 					"text" : descripciones[0].conceptid
				 					}]} ) 
				 			else:
				 				val['resource'].update( {"extension": [{
				 					"url" : "codeSNOMEDInactivo",
				 					"text" : descripciones[0].conceptid
				 					}]} ) 
				 		elif sinonimos:
				 			concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
				 			if concepto.active == '1':
				 				val['resource'].update( {"extension": [{
				 					"url" : "codeSNOMEDActivo",
				 					"text" : sinonimos[0].conceptid
				 					}]} ) 
				 			else:
				 				val['resource'].update( {"extension": [{
				 					"url" : "codeSNOMEDInactivo",
				 					"text" : sinonimos[0].conceptid
				 					}]} ) 
				 		else:
				 			val['resource'].update( {"extension": [{
				 					"url" : "codeSNOMED",
				 					"text" : 0
				 					}]} )
				 			existe = ConceptosNoEncontrados.objects.filter(concepto = data).first()
				 			if not existe:
				 				ConceptosNoEncontrados.objects.create(concepto = data)
			 	print("--- %s seconds Resource Medication ---" % (time.time() - start_time))

		 	if "MedicationAdministration" == val['resource']['resourceType']:
		 		if 'dosage' in val['resource']:
			 		if 'method' in val['resource']['dosage']:
				 		metodo = normalize(val['resource']['dosage']['method'])
		 				descripciones = DescriptionS.objects.filter(term = metodo) & DescriptionS.objects.filter(category_id = 8)
			 			sinonimos = Synonyms.objects.filter(term = metodo)
			 			if descripciones.count() > 1:
				 			for i in descripciones:
				 				con = ConceptS.objects.get(id = i.conceptid)
				 				if con.active == '0':
				 					descripciones = descripciones.exclude(id=i.id)
			 			if sinonimos.count() > 1:
			 	 			for i in sinonimos:
			 		 			con = ConceptS.objects.get(id = i.conceptid)
			 		 			if con.active == '0':
			 		 				sinonimos = sinonimos.exclude(id=i.id)
			 			if descripciones:
			 				concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
			 				if concepto.active == '1':
			 					val['resource'].update( {"extension": [{
			 					"url" : "methodSNOMEDActivo",
			 					"text" : descripciones[0].conceptid
			 					}]} ) 
			 				else:
			 					val['resource'].update( {"extension": [{
			 					"url" : "methodSNOMEDInactivo",
			 					"text" : descripciones[0].conceptid
			 					}]} ) 
			 			elif sinonimos:
			 				concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
			 				if concepto.active == '1':
			 					val['resource'].update( {"extension": [{
			 					"url" : "methodSNOMEDActivo",
			 					"text" : sinonimos[0].conceptid
			 					}]} ) 
			 				else:
			 					val['resource'].update( {"extension": [{
			 					"url" : "methodSNOMEDInactivo",
			 					"text" : sinonimos[0].conceptid
			 					}]} ) 
			 			else:
			 				val['resource'].update( {"extension": [{
			 					"url" : "methodSNOMEDInactivo",
			 					"text" : 0
			 					}]} ) 
			 				existe = ConceptosNoEncontrados.objects.filter(concepto = metodo).first()
				 			if not existe:
				 				ConceptosNoEncontrados.objects.create(concepto = metodo)

			 	if 'dosage' in val['resource']:
			 		if 'route' in val['resource']['dosage']:
			 			#ruta = normalize(val['resource']['dosage']['route'].encode("latin-1").decode("utf-8"))
			 			ruta = normalize(val['resource']['dosage']['route'])
			 			descripciones = DescriptionS.objects.filter(term = ruta) & DescriptionS.objects.filter(category_id = 8)
			 			sinonimos = Synonyms.objects.filter(term = ruta)
			 			if descripciones.count() > 1:
				 			for i in descripciones:
				 				con = ConceptS.objects.get(id = i.conceptid)
				 				if con.active == '0':
				 					descripciones = descripciones.exclude(id=i.id)
			 			if sinonimos.count() > 1:
			 	 			for i in sinonimos:
			 		 			con = ConceptS.objects.get(id = i.conceptid)
			 		 			if con.active == '0':
			 		 				sinonimos = sinonimos.exclude(id=i.id)
			 			if descripciones:
			 				concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
			 				if concepto.active == '1':
			 					val['resource']['extension'].append({
			 					"url" : "rutaSNOMEDActivo",
			 					"text" : descripciones[0].conceptid
			 					} ) 
			 					
			 				else:
			 					val['resource']['extension'].append({
			 					"url" : "rutaSNOMEDInactivo",
			 					"text" : descripciones[0].conceptid
			 					} ) 
		 
		 				elif sinonimos:
		 					concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
		 					if concepto.active == '1':
		 						val['resource']['extension'].append({
			 					"url" : "rutaSNOMEDActivo",
			 					"text" : sinonimos[0].conceptid
			 					} ) 
		 					else:
		 						val['resource']['extension'].append({
			 					"url" : "rutaSNOMEDActivo",
			 					"text" : sinonimos[0].conceptid
			 					} ) 
		 				else:
		 					val['resource']['extension'].append({
			 					"url" : "rutaSNOMED",
			 					"text" : 0
			 					} ) 

		 					existe = ConceptosNoEncontrados.objects.filter(concepto = ruta).first()

				 			if not existe:
				 				ConceptosNoEncontrados.objects.create(concepto = ruta)
			 	print("--- %s seconds Resource MedicationAdministration ---" % (time.time() - start_time))
		 	if "DiagnosticReport" == val['resource']['resourceType']:
		 		if 'conclusionCode' in val['resource']:
		 			if 'text' in val['resource']['conclusionCode']:
		 				conclusionCode = normalize(val['resource']['conclusionCode']['text'])
				 		descripciones = DescriptionS.objects.filter(term = conclusionCode) & DescriptionS.objects.filter(category_id = 6)
				 		sinonimos = Synonyms.objects.filter(term = conclusionCode)
				 		if descripciones.count() > 1:
				 			for i in descripciones:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				descripciones = descripciones.exclude(id=i.id)
					 	if sinonimos.count() > 1:
				 			for i in sinonimos:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				sinonimos = sinonimos.exclude(id=i.id)
				 		if descripciones:
				 			concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
				 			if concepto.active == '1':
				 				val['resource'].update( {"extension": [{
				 					"url" : "conclusionCodeSNOMEDActivo",
				 					"text" : descripciones[0].conceptid
				 					}]} ) 
				 			else:
				 				val['resource'].update( {"extension": [{
				 					"url" : "conclusionCodeSNOMEDInactivo",
			 					"text" : descripciones[0].conceptid
			 					}]} ) 
				 		elif sinonimos:
				 			concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
				 			if concepto.active == '1':
				 				val['resource'].update( {"extension": [{
				 					"url" : "conclusionCodeSNOMEDActivo",
				 					"text" : sinonimos[0].conceptid
				 					}]} ) 
				 			else:
				 				val['resource'].update( {"extension": [{
				 					"url" : "conclusionCodeSNOMEDInactivo",
				 					"text" : sinonimos[0].conceptid
				 					}]} ) 
				 		else:
				 			val['resource'].update( {"extension": [{
				 					"url" : "conclusionCodeSNOMED",
				 					"text" : 0
				 					}]} ) 
				 			existe = ConceptosNoEncontrados.objects.filter(concepto = conclusionCode).first()
				 			if not existe:
				 				ConceptosNoEncontrados.objects.create(concepto = conclusionCode)
			 	if 'conclusion' in val['resource']:
			 		frasePrueba = val['resource']['conclusion'].lower() 
			 		stop_words = set(stopwords.words("spanish"))
			 		frase2 = ""
			 		tokens_frases1 = sent_tokenize(frasePrueba)
			 		
			 		frases_preprocesadas = Parallel(n_jobs=-1, prefer="threads")(delayed(Preprocesamiento)(indx, frases) for indx, frases in enumerate(tokens_frases1))
			 		
			 		frases_preprocesada_ordenada = Sort_0(frases_preprocesadas)
			 		for indx4, item in enumerate(frases_preprocesada_ordenada):
					  if indx4 == 0:
					    frase2 = frase2 + item[1].capitalize()
					  else:
					    frase2 = frase2 + " "+ item[1].capitalize()
			 		frasePrueba = copy.deepcopy(frase2)
			 		frasePrueba = frasePrueba.replace(', ', '. ').lower()

			 		tokens_frases = sent_tokenize(frasePrueba)
			 		fraseFinal = ""
			 		
			 		status_frases = []
			 		try:
				 		if tokens_frases:
				 			status_frases = Parallel(n_jobs=-1, prefer="threads")(delayed(ProcesarOracionFrecuentes)(frases, indx, val, start_time) for indx, frases in enumerate(tokens_frases))
				 			
				 		lista_unos = [i2 for indx2, i2 in enumerate(status_frases) if i2[2] == 1]
				 		lista_final = []
				 		lista_final = Parallel(n_jobs=-1, prefer="threads")(delayed(ProcesarOracion2)(i[1], indx, val, start_time) for indx, i in enumerate(status_frases) if i[2] == 0)
				 		lista_unida = lista_unos + lista_final
				 		lista_unida = Sort_0(lista_unida)

				 		for indx3, item in enumerate(lista_unida):
						  if indx3 == 0:
						    fraseFinal = fraseFinal + item[1].capitalize()
						  else:
						    fraseFinal = fraseFinal + " "+ item[1].capitalize()
				 						 		
				 	except:
				 		pass

				 	if len(status_frases) != 0:
				 		frase_original = val['resource']['conclusion']
				 		if frase_original[-1] != ".":
				 			frase_original = frase_original + "."
				 		if 'ConceptosSNOMED' in val['resource']:
				 			lista_conceptos_encontrados = val['resource']['ConceptosSNOMED']
				 			frase_con_ids = match_con_frase(frase_original, lista_conceptos_encontrados)
				 			val['resource'].update( {"conclusion": frase_con_ids} )
				 		
			 	print("--- %s seconds Resource DiagnosticReport ---" % (time.time() - start_time))	

		 	if "Procedure" == val['resource']['resourceType']:
		 		if 'code' in val['resource']:
		 			if 'text' in val['resource']['code']:
		 				procedimiento = normalize(val['resource']['code']['text'])
			 			descripciones = DescriptionS.objects.filter(term = procedimiento) & DescriptionS.objects.filter(category_id = 4)
			 			sinonimos = Synonyms.objects.filter(term = procedimiento)
			 			if descripciones.count() > 1:
				 			for i in descripciones:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				descripciones = descripciones.exclude(id=i.id)
					 			
					 	if sinonimos.count() > 1:
				 			for i in sinonimos:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				sinonimos = sinonimos.exclude(id=i.id)
					 			
			 			if descripciones:
			 				concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
			 				if concepto.active == '1':
			 					val['resource'].update( {"extension": [{
			 					"url" : "codeSNOMEDActivo",
			 					"text" : descripciones[0].conceptid
			 					}]} ) 
			 				else:
			 					val['resource'].update( {"extension": [{
			 					"url" : "codeSNOMEDInactivo",
			 					"text" : descripciones[0].conceptid
			 					}]} )
			 			elif sinonimos:
			 				concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
			 				if concepto.active == "1":
			 					val['resource'].update( {"extension": [{
			 					"url" : "codeSNOMEDActivo",
			 					"text" : sinonimos[0].conceptid
			 					}]} )
	 						else:
	 							val['resource'].update( {"extension": [{
			 					"url" : "codeSNOMEDInactivo",
			 					"text" : sinonimos[0].conceptid
			 					}]} )
	 					else:
	 						val['resource'] .update( {"extension": [{
			 					"url" : "codeSNOMED",
			 					"text" : 0
			 					}]} )
	 						existe = ConceptosNoEncontrados.objects.filter(concepto = procedimiento).first()
				 			if not existe:
				 				ConceptosNoEncontrados.objects.create(concepto = procedimiento)
		 	
		 		print("--- %s seconds Resource Procedure ---" % (time.time() - start_time))
			 			
		 	if "Observation" == val['resource']['resourceType']:
		 		if 'category' in val['resource']:
		 			for categ in val['resource']['category']:
		 				if 'text' in categ:
		 					categoria = normalize(categ['text'])
		 					descripciones = DescriptionS.objects.filter(term = categoria)
					 		sinonimos = Synonyms.objects.filter(term = categoria)
					 		if descripciones.count() > 1:
					 			for i in descripciones:
						 			con = ConceptS.objects.get(id = i.conceptid)
						 			if con.active == '0':
						 				descripciones = descripciones.exclude(id=i.id)
						 	if sinonimos.count() > 1:
					 			for i in sinonimos:
						 			con = ConceptS.objects.get(id = i.conceptid)
						 			if con.active == '0':
						 				sinonimos = sinonimos.exclude(id=i.id)
					 		if descripciones:
					 			concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
					 			if concepto.active == '1':
					 				val['resource'].update( {"extension": [{
					 					"url" : "categorySNOMEDActivo",
					 					"text" : descripciones[0].conceptid
					 					}]} ) 
					 			else:
					 				val['resource'].update( {"extension": [{
					 					"url" : "categorySNOMEDInactivo",
					 					"text" : descripciones[0].conceptid
					 					}]} )
					 		elif sinonimos:
					 			concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
					 			if concepto.active == '1':
					 				val['resource'].update( {"extension": [{
					 					"url" : "categorySNOMEDActivo",
					 					"text" : sinonimos[0].conceptid
					 					}]} ) 
					 			else:
					 				val['resource'].update( {"extension": [{
					 					"url" : "categorySNOMEDInactivo",
					 					"text" : sinonimos[0].conceptid
					 					}]} ) 

					 		else:
					 			val['resource'].update( {"extension": [{
					 					"url" : "categorySNOMED",
					 					"text" : 0
					 					}]} )
					 			existe = ConceptosNoEncontrados.objects.filter(concepto = categoria).first()
					 			if not existe:
					 				ConceptosNoEncontrados.objects.create(concepto = categoria)
		 		if 'code' in val['resource']:
		 			if 'text' in val['resource']['code']:
		 				code = normalize(val['resource']['code']['text'])					 				
				 		descripciones = DescriptionS.objects.filter(term = code)
				 		sinonimos = Synonyms.objects.filter(term = code)
				 		if descripciones.count() > 1:
				 			for i in descripciones:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				descripciones = descripciones.exclude(id=i.id)
					 			
					 	if sinonimos.count() > 1:
				 			for i in sinonimos:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				sinonimos = sinonimos.exclude(id=i.id)
					 			
					 	if descripciones:
				 			concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
				 			if concepto.active == '1':
				 				val['resource']['extension'].append({
				 					"url" : "codeSNOMEDActivo",
				 					"text" : descripciones[0].conceptid
				 					} ) 
				 			else:
				 				val['resource']['extension'].append({
				 					"url" : "codeSNOMEDInactivo",
				 					"text" : descripciones[0].conceptid
				 					} ) 
				 		elif sinonimos:
				 			concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
				 			if concepto.active == '1':
				 				val['resource']['extension'].append({
				 					"url" : "codeSNOMEDActivo",
				 					"text" : sinonimos[0].conceptid
				 					} ) 
				 			else:
				 				val['resource']['extension'].append({
				 					"url" : "codeSNOMEDInactivo",
				 					"text" : sinonimos[0].conceptid
				 					} ) 
		 				else:
		 					if 'extension' not in val['resource']:
		 						val['resource'].update( {"extension": [{
					 					"url" : "codeSNOMED",
					 					"text" : 0
					 					}]} )
		 					else:
		 						val['resource']['extension'].append({
					 					"url" : "codeSNOMED",
					 					"text" : 0
					 					} ) 
		 					existe = ConceptosNoEncontrados.objects.filter(concepto = code).first()

				 			if not existe:
				 				ConceptosNoEncontrados.objects.create(concepto = code)
			 	print("--- %s seconds Resource Observation ---" % (time.time() - start_time))

		 data=""
		 print("--- %s seconds ---" % (time.time() - start_time))
		 return Response(responseMA)
	else:
		return Response(status=status.HTTP_400_BAD_REQUEST)

@api_view(['POST'])
def ProcesarDiagnosticReportView(request):
	responseMA = request.data
	if (responseMA):
		recurso = responseMA['resourceType']
		if (recurso == 'DiagnosticReport'):
			start_time = time.time()
			if 'conclusionCode' in responseMA:
		 			if 'text' in responseMA['conclusionCode']:
		 				conclusionCode = normalize(responseMA['conclusionCode']['text'])
		 				#conclusionCode = normalize(codD['display'])
				 		descripciones = DescriptionS.objects.filter(term = conclusionCode) & DescriptionS.objects.filter(category_id = 6)
				 		sinonimos = Synonyms.objects.filter(term = conclusionCode)
				 		if descripciones.count() > 1:
				 			for i in descripciones:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				descripciones = descripciones.exclude(id=i.id)
					 	if sinonimos.count() > 1:
				 			for i in sinonimos:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				sinonimos = sinonimos.exclude(id=i.id)
				 		if descripciones:
				 			concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
				 			if concepto.active == '1':
				 				responseMA.update( {"extension": [{
				 					"url" : "conclusionCodeSNOMEDActivo",
				 					"text" : descripciones[0].conceptid
				 					}]} ) 
				 			else:
				 				responseMA.update( {"extension": [{
				 					"url" : "conclusionCodeSNOMEDInactivo",
				 					"text" : descripciones[0].conceptid
				 					}]} ) 
				 		elif sinonimos:
				 			concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
				 			if concepto.active == '1':
				 				responseMA.update( {"extension": [{
				 					"url" : "conclusionCodeSNOMEDActivo",
				 					"text" : sinonimos[0].conceptid
				 					}]} ) 
				 			else:
				 				responseMA.update( {"extension": [{
				 					"url" : "conclusionCodeSNOMEDInactivo",
				 					"text" : sinonimos[0].conceptid
				 					}]} ) 
				 		else:
				 			responseMA.update( {"extension": [{
				 					"url" : "conclusionCodeSNOMED",
				 					"text" : 0
				 					}]} ) 
				 			if conclusionCode != "":	 				
					 			existe = ConceptosNoEncontrados.objects.filter(concepto = conclusionCode).first()
					 			if not existe:
					 				ConceptosNoEncontrados.objects.create(concepto = conclusionCode)
			if 'conclusion' in responseMA:
		 		
		 		frasePrueba = responseMA['conclusion'].lower()
		 		stop_words = set(stopwords.words("spanish"))
		 		frase2 = ""
		 		tokens_frases1 = sent_tokenize(frasePrueba)
		 		frases_preprocesadas = Parallel(n_jobs=-1, prefer="threads")(delayed(Preprocesamiento)(indx, frases) for indx, frases in enumerate(tokens_frases1))
		 		
		 		frases_preprocesada_ordenada = Sort_0(frases_preprocesadas)
		 		for indx4, item in enumerate(frases_preprocesada_ordenada):
				  if indx4 == 0:
				    frase2 = frase2 + item[1].capitalize()
				  else:
				    frase2 = frase2 + " "+ item[1].capitalize()
		 		frasePrueba = copy.deepcopy(frase2)
		 		
		 		frasePrueba = frasePrueba.replace(', ', '. ').lower()
		 		tokens_frases = sent_tokenize(frasePrueba)
		 		
		 		fraseFinal = ""
		 		
		 		status_frases = []
		 		try:
			 		if tokens_frases:
			 			status_frases = Parallel(n_jobs=-1, prefer="threads")(delayed(ProcesarOracionFrecuentes)(frases, indx, responseMA, start_time) for indx, frases in enumerate(tokens_frases))
			 			
			 		lista_unos = [i2 for indx2, i2 in enumerate(status_frases) if i2[2] == 1]
			 		lista_final = []
			 		lista_final = Parallel(n_jobs=-1, prefer="threads")(delayed(ProcesarOracion2)(i[1], indx, responseMA, start_time) for indx, i in enumerate(status_frases) if i[2] == 0)
			 		lista_unida = lista_unos + lista_final
			 		lista_unida = Sort_0(lista_unida)

			 		for indx3, item in enumerate(lista_unida):
			 		  if indx3 == 0:
			 		    fraseFinal = fraseFinal + item[1].capitalize()
			 		  else:
			 		    fraseFinal = fraseFinal + " "+ item[1].capitalize()
			 		
		 		except:
		 			pass

		 		if len(status_frases) != 0:
			 		frase_original = responseMA['conclusion']
			 		if frase_original[-1] != ".":
			 			frase_original = frase_original + "."
			 		if 'ConceptosSNOMED' in responseMA:
				 			lista_conceptos_encontrados = responseMA['ConceptosSNOMED']
				 			frase_con_ids = match_con_frase(frase_original, lista_conceptos_encontrados)
				 			responseMA.update( {"conclusion": frase_con_ids} )
			 		
			print("--- %s seconds Resource DiagnosticReport alone ---" % (time.time() - start_time))	
			return Response(responseMA)
		else:
			return Response(status=status.HTTP_400_BAD_REQUEST)
	else:
		return Response(status=status.HTTP_400_BAD_REQUEST)

@api_view(['POST'])
def ProcesarMedicationView(request):
	responseMA = request.data
	if (responseMA):
		recurso = responseMA['resourceType']
		if (recurso == 'Medication'):
			start_time = time.time()
			if 'code' in responseMA:				
				if 'text' in responseMA['code']:
					data = normalize(responseMA['code']['text'])
					#data = normalize(val['resource']['code'].encode("latin-1").decode("utf-8"))
					descripciones = DescriptionS.objects.filter(term = data) & DescriptionS.objects.filter(category_id = 10)
					sinonimos = Synonyms.objects.filter(term = data)
					if descripciones.count() > 1:
						for i in descripciones:
				 			con = ConceptS.objects.get(id = i.conceptid)
				 			if con.active == '0':
				 				descripciones = descripciones.exclude(id=i.id)
					if sinonimos.count() > 1:
			 			for i in sinonimos:
				 			con = ConceptS.objects.get(id = i.conceptid)
				 			if con.active == '0':
				 				sinonimos = sinonimos.exclude(id=i.id)
					if descripciones:
			 			concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
			 			if concepto.active == '1':
			 				responseMA.update( {"extension": [{
			 					"url" : "codeSNOMEDActivo",
			 					"text" : descripciones[0].conceptid
			 					}]} ) 
			 			else:
			 				responseMA.update( {"extension": [{
			 					"url" : "codeSNOMEDInactivo",
			 					"text" : descripciones[0].conceptid
			 					}]} ) 
					elif sinonimos:
			 			concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
			 			if concepto.active == '1':
			 				responseMA.update( {"extension": [{
			 					"url" : "codeSNOMEDActivo",
			 					"text" : sinonimos[0].conceptid
			 					}]} ) 
			 			else:
			 				responseMA.update( {"extension": [{
			 					"url" : "codeSNOMEDInactivo",
			 					"text" : sinonimos[0].conceptid
			 					}]} ) 
					else:
			 			responseMA.update( {"extension": [{
			 					"url" : "codeSNOMED",
			 					"text" : 0
			 					}]} )
			 			existe = ConceptosNoEncontrados.objects.filter(concepto = data).first()
			 			if not existe:
			 				ConceptosNoEncontrados.objects.create(concepto = data)
			print("--- %s seconds Resource Medication ---" % (time.time() - start_time))
			return Response(responseMA)
		else:
			return Response(status=status.HTTP_400_BAD_REQUEST)
	else:
		return Response(status=status.HTTP_400_BAD_REQUEST)

@api_view(['POST'])
def ProcesarMedicationAdministrationView(request):
	responseMA = request.data
	if (responseMA):
		recurso = responseMA['resourceType']
		if (recurso == 'MedicationAdministration'):
			start_time = time.time()
			if 'dosage' in responseMA:
		 		if 'method' in responseMA['dosage']:
			 		metodo = normalize(responseMA['dosage']['method'])
	 				descripciones = DescriptionS.objects.filter(term = metodo) & DescriptionS.objects.filter(category_id = 8)
		 			sinonimos = Synonyms.objects.filter(term = metodo)
		 			if descripciones.count() > 1:
			 			for i in descripciones:
			 				con = ConceptS.objects.get(id = i.conceptid)
			 				if con.active == '0':
			 					descripciones = descripciones.exclude(id=i.id)
		 			if sinonimos.count() > 1:
		 	 			for i in sinonimos:
		 		 			con = ConceptS.objects.get(id = i.conceptid)
		 		 			if con.active == '0':
		 		 				sinonimos = sinonimos.exclude(id=i.id)
		 			if descripciones:
		 				concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
		 				if concepto.active == '1':
		 					responseMA.update( {"extension": [{
		 					"url" : "methodSNOMEDActivo",
		 					"text" : descripciones[0].conceptid
		 					}]} ) 
		 				else:
		 					responseMA.update( {"extension": [{
		 					"url" : "methodSNOMEDInactivo",
		 					"text" : descripciones[0].conceptid
		 					}]} ) 
		 			elif sinonimos:
		 				concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
		 				if concepto.active == '1':
		 					responseMA.update( {"extension": [{
		 					"url" : "methodSNOMEDActivo",
		 					"text" : sinonimos[0].conceptid
		 					}]} ) 
		 				else:
		 					responseMA.update( {"extension": [{
		 					"url" : "methodSNOMEDInactivo",
		 					"text" : sinonimos[0].conceptid
		 					}]} ) 
		 			else:
		 				responseMA.update( {"extension": [{
		 					"url" : "methodSNOMEDInactivo",
		 					"text" : 0
		 					}]} ) 
		 				existe = ConceptosNoEncontrados.objects.filter(concepto = metodo).first()
			 			if not existe:
			 				ConceptosNoEncontrados.objects.create(concepto = metodo)

			if 'dosage' in responseMA:
		 		if 'route' in responseMA['dosage']:
		 			#ruta = normalize(val['resource']['dosage']['route'].encode("latin-1").decode("utf-8"))
		 			ruta = normalize(responseMA['dosage']['route'])
		 			descripciones = DescriptionS.objects.filter(term = ruta) & DescriptionS.objects.filter(category_id = 8)
		 			sinonimos = Synonyms.objects.filter(term = ruta)
		 			if descripciones.count() > 1:
			 			for i in descripciones:
			 				con = ConceptS.objects.get(id = i.conceptid)
			 				if con.active == '0':
			 					descripciones = descripciones.exclude(id=i.id)
		 			if sinonimos.count() > 1:
		 	 			for i in sinonimos:
		 		 			con = ConceptS.objects.get(id = i.conceptid)
		 		 			if con.active == '0':
		 		 				sinonimos = sinonimos.exclude(id=i.id)
		 			if descripciones:
		 				concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
		 				if concepto.active == '1':
		 					responseMA['extension'].append({
		 					"url" : "rutaSNOMEDActivo",
		 					"text" : descripciones[0].conceptid
		 					} ) 
		 					
		 				else:
		 					responseMA['extension'].append({
		 					"url" : "rutaSNOMEDInactivo",
		 					"text" : descripciones[0].conceptid
		 					} ) 
	 
	 				elif sinonimos:
	 					concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
	 					if concepto.active == '1':
	 						responseMA['extension'].append({
		 					"url" : "rutaSNOMEDActivo",
		 					"text" : sinonimos[0].conceptid
		 					} ) 
	 					else:
	 						responseMA['extension'].append({
		 					"url" : "rutaSNOMEDActivo",
		 					"text" : sinonimos[0].conceptid
		 					} ) 
	 				else:
	 					responseMA['extension'].append({
		 					"url" : "rutaSNOMED",
		 					"text" : 0
		 					} ) 
	 					existe = ConceptosNoEncontrados.objects.filter(concepto = ruta).first()
			 			if not existe:
			 				ConceptosNoEncontrados.objects.create(concepto = ruta)
			print("--- %s seconds Resource MedicationAdministration ---" % (time.time() - start_time))

			return Response(responseMA)
	else:
		return Response(status=status.HTTP_400_BAD_REQUEST)

@api_view(['POST'])
def ProcesarProcedureView(request):
	responseMA = request.data
	if (responseMA):
		recurso = responseMA['resourceType']
		if (recurso == 'Procedure'):
			start_time = time.time()
			if 'code' in responseMA:				
				if 'text' in responseMA['code']:
					procedimiento = normalize(responseMA['code']['text'])
					descripciones = DescriptionS.objects.filter(term = procedimiento) & DescriptionS.objects.filter(category_id = 4)
					sinonimos = Synonyms.objects.filter(term = procedimiento)
					if descripciones.count() > 1:
			 			for i in descripciones:
				 			con = ConceptS.objects.get(id = i.conceptid)
				 			if con.active == '0':
				 				descripciones = descripciones.exclude(id=i.id)
				 			
					if sinonimos.count() > 1:
			 			for i in sinonimos:
				 			con = ConceptS.objects.get(id = i.conceptid)
				 			if con.active == '0':
				 				sinonimos = sinonimos.exclude(id=i.id)
				 			
					if descripciones:
		 				concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
		 				if concepto.active == '1':
		 					responseMA.update( {"extension": [{
		 					"url" : "codeSNOMEDActivo",
		 					"text" : descripciones[0].conceptid
		 					}]} ) 
		 				else:
		 					responseMA.update( {"extension": [{
		 					"url" : "codeSNOMEDInactivo",
		 					"text" : descripciones[0].conceptid
		 					}]} )
					elif sinonimos:
		 				concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
		 				if concepto.active == "1":
		 					responseMA.update( {"extension": [{
		 					"url" : "codeSNOMEDActivo",
		 					"text" : sinonimos[0].conceptid
		 					}]} )
		 				else:
		 					responseMA.update( {"extension": [{
		 					"url" : "codeSNOMEDInactivo",
		 					"text" : sinonimos[0].conceptid
		 					}]} )
					else:
		 				responseMA .update( {"extension": [{
		 					"url" : "codeSNOMED",
		 					"text" : 0
		 					}]} )
		 				existe = ConceptosNoEncontrados.objects.filter(concepto = procedimiento).first()
			 			if not existe:
			 				ConceptosNoEncontrados.objects.create(concepto = procedimiento)
			print("--- %s seconds Resource Procedure ---" % (time.time() - start_time))
			return Response(responseMA)
		else:
			return Response(status=status.HTTP_400_BAD_REQUEST)
	else:
		return Response(status=status.HTTP_400_BAD_REQUEST)

@api_view(['POST'])
def ProcesarObservationView(request):
	responseMA = request.data
	if (responseMA):
		recurso = responseMA['resourceType']
		if (recurso == 'Observation'):
			start_time = time.time()
			if 'category' in responseMA:
				for categ in responseMA['category']:
					if 'text' in categ:
					 	categoria = normalize(categ['text'])
						#categoria = normalize(cod['display'])
				 		descripciones = DescriptionS.objects.filter(term = categoria)
				 		sinonimos = Synonyms.objects.filter(term = categoria)
				 		if descripciones.count() > 1:
				 			for i in descripciones:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				descripciones = descripciones.exclude(id=i.id)
					 	if sinonimos.count() > 1:
				 			for i in sinonimos:
					 			con = ConceptS.objects.get(id = i.conceptid)
					 			if con.active == '0':
					 				sinonimos = sinonimos.exclude(id=i.id)
				 		if descripciones:
				 			concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
				 			if concepto.active == '1':
				 				responseMA.update( {"extension": [{
				 					"url" : "categorySNOMEDActivo",
				 					"text" : descripciones[0].conceptid
				 					}]} ) 
				 			else:
				 				responseMA.update( {"extension": [{
				 					"url" : "categorySNOMEDInactivo",
				 					"text" : descripciones[0].conceptid
				 					}]} )
				 		elif sinonimos:
				 			concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
				 			if concepto.active == '1':
				 				responseMA.update( {"extension": [{
				 					"url" : "categorySNOMEDActivo",
				 					"text" : sinonimos[0].conceptid
				 					}]} ) 
				 			else:
				 				responseMA.update( {"extension": [{
				 					"url" : "categorySNOMEDInactivo",
				 					"text" : sinonimos[0].conceptid
				 					}]} ) 

				 		else:
				 			responseMA.update( {"extension": [{
				 					"url" : "categorySNOMED",
				 					"text" : 0
				 					}]} )
				 			existe = ConceptosNoEncontrados.objects.filter(concepto = categoria).first()
				 			if not existe:
				 				ConceptosNoEncontrados.objects.create(concepto = categoria)

			if 'code' in responseMA:
				if 'text' in responseMA['code']:
					code = normalize(responseMA['code']['text'])
					#code = normalize(cod3['display'])
					descripciones = DescriptionS.objects.filter(term = code)
					sinonimos = Synonyms.objects.filter(term = code)
					if descripciones.count() > 1:
			 			for i in descripciones:
				 			con = ConceptS.objects.get(id = i.conceptid)
				 			if con.active == '0':
				 				descripciones = descripciones.exclude(id=i.id)
				 			
					if sinonimos.count() > 1:
			 			for i in sinonimos:
				 			con = ConceptS.objects.get(id = i.conceptid)
				 			if con.active == '0':
				 				sinonimos = sinonimos.exclude(id=i.id)
				 			
					if descripciones:
			 			concepto = ConceptS.objects.get(id = descripciones[0].conceptid)
			 			if concepto.active == '1':
			 				responseMA['extension'].append({
			 					"url" : "codeSNOMEDActivo",
			 					"text" : descripciones[0].conceptid
			 					} ) 
			 			else:
			 				responseMA['extension'].append({
			 					"url" : "codeSNOMEDInactivo",
			 					"text" : descripciones[0].conceptid
			 					} ) 
					elif sinonimos:
			 			concepto = ConceptS.objects.get(id = sinonimos[0].conceptid)
			 			if concepto.active == '1':
			 				responseMA['extension'].append({
			 					"url" : "codeSNOMEDActivo",
			 					"text" : sinonimos[0].conceptid
			 					} ) 
			 			else:
			 				responseMA['extension'].append({
			 					"url" : "codeSNOMEDInactivo",
			 					"text" : sinonimos[0].conceptid
			 					} ) 
					else:
						if 'extension' not in responseMA:
							responseMA.update( {"extension": [{
				 					"url" : "codeSNOMED",
				 					"text" : 0
				 					}]} )
						else:
							responseMA['extension'].append({
			 					"url" : "codeSNOMED",
			 					"text" : 0
			 					} )
						existe = ConceptosNoEncontrados.objects.filter(concepto = code).first()
						if not existe:
			 				ConceptosNoEncontrados.objects.create(concepto = code)
			print("--- %s seconds Resource Observation ---" % (time.time() - start_time))
			return Response(responseMA)
		else:
			return Response(status=status.HTTP_400_BAD_REQUEST)
	else:
		return Response(status=status.HTTP_400_BAD_REQUEST)