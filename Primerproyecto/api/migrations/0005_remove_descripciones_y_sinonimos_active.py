# Generated by Django 3.2.7 on 2022-03-07 21:54

from django.db import migrations


class Migration(migrations.Migration):

    dependencies = [
        ('api', '0004_descripciones_y_sinonimos'),
    ]

    operations = [
        migrations.RemoveField(
            model_name='descripciones_y_sinonimos',
            name='active',
        ),
    ]