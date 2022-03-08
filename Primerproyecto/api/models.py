from django.db import models

class TokensDiagnosticos(models.Model):
    #id = models.CharField(max_length=36, primary_key=True)
    token = models.CharField(max_length=255)
    id_descripcion = models.CharField(max_length=255)
    largo_palabras_termino = models.IntegerField()
# Create your models here.

class TokensDiagnosticosFrecuentes(models.Model):
    #id = models.CharField(max_length=36, primary_key=True)
    token = models.CharField(max_length=255)
    id_descripcion = models.CharField(max_length=255)
    largo_palabras_termino = models.IntegerField()

class TokensProcedures(models.Model):
    #id = models.CharField(max_length=36, primary_key=True)
    token = models.CharField(max_length=255)
    id_descripcion = models.CharField(max_length=255)
    largo_palabras_termino = models.IntegerField()

class Descripciones_y_sinonimos(models.Model):
    id = models.CharField(max_length=18, primary_key=True)
    conceptid = models.CharField(max_length=18)
    typeid = models.CharField(max_length=18)
    term = models.CharField(max_length=255)
    created_at = models.DateTimeField(auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)