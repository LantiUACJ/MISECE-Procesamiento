# This is an auto-generated Django model module.
# You'll have to do the following manually to clean this up:
#   * Rearrange models' order
#   * Make sure each model has one field with primary_key=True
#   * Make sure each ForeignKey and OneToOneField has `on_delete` set to the desired behavior
#   * Remove `managed = False` lines if you wish to allow Django to create, modify, and delete the table
# Feel free to rename the models, but don't rename db_table values or field names.
from django.db import models


class ConceptosNoEncontrados(models.Model):
    #id = models.CharField(max_length=36, primary_key=True)
    concepto = models.CharField(max_length=255)
    created_at = models.DateTimeField(auto_now_add=True)
    updated_at = models.DateTimeField(auto_now=True)

class AssociationrefsetS(models.Model):
    id = models.CharField(max_length=36, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    refsetid = models.CharField(max_length=18)
    referencedcomponentid = models.CharField(max_length=18)
    targetcomponentid = models.CharField(max_length=18)

    class Meta:
        managed = False
        db_table = 'associationrefset_s'


class AttributevaluerefsetS(models.Model):
    id = models.CharField(max_length=36, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    refsetid = models.CharField(max_length=18)
    referencedcomponentid = models.CharField(max_length=18)
    valueid = models.CharField(max_length=18)

    class Meta:
        managed = False
        db_table = 'attributevaluerefset_s'


class Categories(models.Model):
    id = models.BigAutoField(primary_key=True)
    name = models.CharField(max_length=191)
    created_at = models.DateTimeField(blank=True, null=True)
    updated_at = models.DateTimeField(blank=True, null=True)
    conceptid = models.CharField(max_length=191, blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'categories'


class ComplexmaprefsetF(models.Model):
    id = models.CharField(max_length=36, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    refsetid = models.CharField(max_length=18)
    referencedcomponentid = models.CharField(max_length=18)
    mapgroup = models.SmallIntegerField(db_column='mapGroup')  # Field name made lowercase.
    mappriority = models.SmallIntegerField(db_column='mapPriority')  # Field name made lowercase.
    maprule = models.TextField(db_column='mapRule', blank=True, null=True)  # Field name made lowercase.
    mapadvice = models.TextField(db_column='mapAdvice', blank=True, null=True)  # Field name made lowercase.
    maptarget = models.CharField(db_column='mapTarget', max_length=18, blank=True, null=True)  # Field name made lowercase.
    correlationid = models.CharField(db_column='correlationId', max_length=18)  # Field name made lowercase.

    class Meta:
        managed = False
        db_table = 'complexmaprefset_f'


class ConceptFinisheds(models.Model):
    id = models.BigAutoField(primary_key=True)
    level = models.CharField(max_length=191)
    user_id = models.IntegerField()
    conceptid = models.CharField(max_length=191)
    created_at = models.DateTimeField(blank=True, null=True)
    updated_at = models.DateTimeField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'concept_finisheds'


class ConceptS(models.Model):
    id = models.CharField(max_length=18, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    definitionstatusid = models.CharField(max_length=18)
    category_id = models.IntegerField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'concept_s'


class DescriptionS(models.Model):
    id = models.CharField(max_length=18, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    conceptid = models.CharField(max_length=18)
    languagecode = models.CharField(max_length=2)
    typeid = models.CharField(max_length=18)
    term = models.CharField(max_length=255)
    casesignificanceid = models.CharField(max_length=18)
    category_id = models.IntegerField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'description_s'


class ExtendedmaprefsetS(models.Model):
    id = models.CharField(max_length=36, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    refsetid = models.CharField(max_length=18)
    referencedcomponentid = models.CharField(max_length=18)
    mapgroup = models.SmallIntegerField(db_column='mapGroup')  # Field name made lowercase.
    mappriority = models.SmallIntegerField(db_column='mapPriority')  # Field name made lowercase.
    maprule = models.TextField(db_column='mapRule', blank=True, null=True)  # Field name made lowercase.
    mapadvice = models.TextField(db_column='mapAdvice', blank=True, null=True)  # Field name made lowercase.
    maptarget = models.CharField(db_column='mapTarget', max_length=18, blank=True, null=True)  # Field name made lowercase.
    correlationid = models.CharField(db_column='correlationId', max_length=18)  # Field name made lowercase.
    mapcategoryid = models.CharField(db_column='mapCategoryId', max_length=18, blank=True, null=True)  # Field name made lowercase.

    class Meta:
        managed = False
        db_table = 'extendedmaprefset_s'


class FailedJobs(models.Model):
    id = models.BigAutoField(primary_key=True)
    uuid = models.CharField(unique=True, max_length=191)
    connection = models.TextField()
    queue = models.TextField()
    payload = models.TextField()
    exception = models.TextField()
    failed_at = models.DateTimeField()

    class Meta:
        managed = False
        db_table = 'failed_jobs'


class LangrefsetS(models.Model):
    id = models.CharField(max_length=36, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    refsetid = models.CharField(max_length=18)
    referencedcomponentid = models.CharField(max_length=18)
    acceptabilityid = models.CharField(max_length=18)

    class Meta:
        managed = False
        db_table = 'langrefset_s'


class Migrations(models.Model):
    migration = models.CharField(max_length=191)
    batch = models.IntegerField()

    class Meta:
        managed = False
        db_table = 'migrations'


class OwlexpressionS(models.Model):
    id = models.CharField(max_length=36, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    refsetid = models.CharField(max_length=18)
    referencedcomponentid = models.CharField(max_length=18)
    owlexpression = models.TextField(db_column='owlExpression')  # Field name made lowercase.

    class Meta:
        managed = False
        db_table = 'owlexpression_s'


class PasswordResets(models.Model):
    email = models.CharField(max_length=191)
    token = models.CharField(max_length=191)
    created_at = models.DateTimeField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'password_resets'


class RelationshipS(models.Model):
    id = models.CharField(max_length=18, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    sourceid = models.CharField(max_length=18)
    destinationid = models.CharField(max_length=18)
    relationshipgroup = models.CharField(max_length=18)
    typeid = models.CharField(max_length=18)
    characteristictypeid = models.CharField(max_length=18)
    modifierid = models.CharField(max_length=18)

    class Meta:
        managed = False
        db_table = 'relationship_s'


class Rols(models.Model):
    id = models.BigAutoField(primary_key=True)
    name = models.CharField(max_length=191)
    created_at = models.DateTimeField(blank=True, null=True)
    updated_at = models.DateTimeField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'rols'


class SimplemaprefsetS(models.Model):
    id = models.CharField(max_length=36, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    refsetid = models.CharField(max_length=18)
    referencedcomponentid = models.CharField(max_length=18)
    maptarget = models.CharField(max_length=32)

    class Meta:
        managed = False
        db_table = 'simplemaprefset_s'


class SimplerefsetS(models.Model):
    id = models.CharField(max_length=36, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    refsetid = models.CharField(max_length=18)
    referencedcomponentid = models.CharField(max_length=18)

    class Meta:
        managed = False
        db_table = 'simplerefset_s'


class StatedRelationshipS(models.Model):
    id = models.CharField(max_length=18, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    sourceid = models.CharField(max_length=18)
    destinationid = models.CharField(max_length=18)
    relationshipgroup = models.CharField(max_length=18)
    typeid = models.CharField(max_length=18)
    characteristictypeid = models.CharField(max_length=18)
    modifierid = models.CharField(max_length=18)

    class Meta:
        managed = False
        db_table = 'stated_relationship_s'


class SynonymVotes(models.Model):
    id = models.BigAutoField(primary_key=True)
    level = models.CharField(max_length=191)
    user_id = models.IntegerField()
    synonym_id = models.CharField(max_length=191)
    like = models.IntegerField(blank=True, null=True)
    dislike = models.IntegerField(blank=True, null=True)
    delete = models.IntegerField(blank=True, null=True)
    created_at = models.DateTimeField(blank=True, null=True)
    updated_at = models.DateTimeField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'synonym_votes'


class Synonyms(models.Model):
    term = models.CharField(max_length=256)
    conceptid = models.CharField(max_length=18)
    delete = models.IntegerField()
    created_at = models.DateTimeField(blank=True, null=True)
    updated_at = models.DateTimeField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'synonyms'


class SynonymsUpdates(models.Model):
    id = models.BigAutoField(primary_key=True)
    synonym_id = models.IntegerField()
    user_id = models.IntegerField()
    update = models.CharField(max_length=191)
    old_value = models.CharField(max_length=191)
    new_value = models.CharField(max_length=191)
    created_at = models.DateTimeField(blank=True, null=True)
    updated_at = models.DateTimeField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'synonyms_updates'


class TextdefinitionS(models.Model):
    id = models.CharField(max_length=18, primary_key=True)
    effectivetime = models.CharField(max_length=8)
    active = models.CharField(max_length=1)
    moduleid = models.CharField(max_length=18)
    conceptid = models.CharField(max_length=18)
    languagecode = models.CharField(max_length=2)
    typeid = models.CharField(max_length=18)
    term = models.CharField(max_length=4096)
    casesignificanceid = models.CharField(max_length=18)

    class Meta:
        managed = False
        db_table = 'textdefinition_s'


class TypeCategories(models.Model):
    id = models.BigAutoField(primary_key=True)
    category_id = models.IntegerField()
    type_id = models.IntegerField()
    created_at = models.DateTimeField(blank=True, null=True)
    updated_at = models.DateTimeField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'type_categories'


class Types(models.Model):
    id = models.BigAutoField(primary_key=True)
    name = models.CharField(max_length=191)
    created_at = models.DateTimeField(blank=True, null=True)
    updated_at = models.DateTimeField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'types'


class UserProfiles(models.Model):
    id = models.BigAutoField(primary_key=True)
    name = models.CharField(max_length=191)
    apellido_p = models.CharField(max_length=191)
    apellido_m = models.CharField(max_length=191)
    curp = models.CharField(max_length=191, blank=True, null=True)
    birtdate = models.DateTimeField()
    born_state = models.CharField(max_length=191)
    born_city = models.CharField(max_length=191)
    hospital_institution = models.CharField(max_length=191)
    cedula = models.CharField(max_length=191, blank=True, null=True)
    position = models.CharField(max_length=191)
    last_degree = models.CharField(max_length=191)
    user_id = models.IntegerField()
    created_at = models.DateTimeField(blank=True, null=True)
    updated_at = models.DateTimeField(blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'user_profiles'


class Users(models.Model):
    id = models.BigAutoField(primary_key=True)
    name = models.CharField(max_length=191)
    email = models.CharField(unique=True, max_length=191)
    email_verified_at = models.DateTimeField(blank=True, null=True)
    password = models.CharField(max_length=191)
    remember_token = models.CharField(max_length=100, blank=True, null=True)
    created_at = models.DateTimeField(blank=True, null=True)
    updated_at = models.DateTimeField(blank=True, null=True)
    type_id = models.IntegerField(blank=True, null=True)
    delete = models.IntegerField()
    rol_id = models.IntegerField()
    email_validation_token = models.CharField(max_length=191, blank=True, null=True)

    class Meta:
        managed = False
        db_table = 'users'
