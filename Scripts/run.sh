#!/bin/bash
sudo apt update -y > /dev/null 2> /dev/null < /dev/null &
cd /
cd var/www/html/MISECE-Procesamiento/Procesamiento_SNOMED/Procesamiento_SNOMED/
sudo rm settings.py
echo removed 
sudo aws s3 cp s3://s3procesamiento/settings.py /var/www/html/MISECE-Procesamiento/Procesamiento_SNOMED/Procesamiento_SNOMED/ > /dev/null 2> /dev/null < /dev/null &