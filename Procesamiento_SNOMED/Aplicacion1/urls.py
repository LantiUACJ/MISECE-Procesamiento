"""from django.urls import path, include
from operadores.views import registro, activos, index, correcto, no
from operadores.views import Registro_crear#registro_crear"""
from django.urls import path
from . import views
#from flotaVehicular.settings import DEBUG, STATIC_URL, STATIC_ROOT, MEDIA_URL, MEDIA_ROOT
from django.conf.urls.static import static
from django.contrib.auth import views as auth_views
from django.views.generic.base import RedirectView
from .views import *
app_name='aplicacion1'

urlpatterns = [
    path('index', views.InicioView, name='index')
]

