import requests
import json

def generarRequest(url, params={}):
	response = requests.get(url, params, headers={'Accept': 'application/fhir+json'})
	return response.json()

def normalize(s):
	#print("entre a normalize")
	replacements = (("á", "a"),("é", "e"),("í", "i"),("ó", "o"),("ú", "u"),)
	if type(s) == str:

		for a, b in replacements:
			s = s.replace(a, b).replace(a.upper(), b.upper())
		return s
	else:
		return s

def validateJSON(jsonData):
    try:
        json.loads(jsonData)
    except ValueError as err:
        return False
    return True