from django.urls import path
from . import views

urlpatterns = [
	path('', views.apiOverview, name =  "api-overview"),
	path('procesarSNOMED/Bundle', views.ProcesarBundleView, name =  "api-procesarBundleSNOMED"),
	path('procesarSNOMED/DiagnosticReport', views.ProcesarDiagnosticReportView, name =  "api-procesarDiagnosticReportSNOMED"),
	path('procesarSNOMED/Medication', views.ProcesarMedicationView, name =  "api-procesarMedicationSNOMED"),
	path('procesarSNOMED/MedicationAdministration', views.ProcesarMedicationAdministrationView, name =  "api-procesarMedicationAdministrationSNOMED"),
	path('procesarSNOMED/Procedure', views.ProcesarProcedureView, name =  "api-procesarProcedureSNOMED"),
	path('procesarSNOMED/Observation', views.ProcesarObservationView, name =  "api-procesarObservationSNOMED"),
	path('procesarSNOMED/AWSBundle', views.ProcesarAWSBundleView, name =  "api-procesarObservationSNOMED"),
	]