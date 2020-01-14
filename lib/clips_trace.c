#include "stdio.h"
#include "setup.h"
#include "factrhs.h"
#include "tmpltutl.h"


// Copied from facthsh.c
static struct fact *FactExists(
  void *theEnv,
  struct fact *theFact,
  unsigned long hashValue)
  {
   struct factHashEntry *theFactHash;

   if (FactData(theEnv)->FactHashTableSize == 0)
       return (NULL);
   hashValue = (hashValue % FactData(theEnv)->FactHashTableSize);

   for (theFactHash = FactData(theEnv)->FactHashTable[hashValue];
        theFactHash != NULL;
        theFactHash = theFactHash->next)
     {
      if (theFact->hashValue != theFactHash->theFact->hashValue)
        { continue; }

      if ((theFact->whichDeftemplate == theFactHash->theFact->whichDeftemplate) ?
          MultifieldsEqual(&theFact->theProposition,
                           &theFactHash->theFact->theProposition) : FALSE)
        { return(theFactHash->theFact); }
     }

   return(NULL);
  }

// Copied from AssertCommand (factcom.c)
int assert_with_trace(void *theEnv)
{
   struct deftemplate *theDeftemplate;
   struct field *theField;
   DATA_OBJECT theValue;
   struct expr *theExpression;
   struct templateSlot *slotPtr;
   struct fact *newFact;
   int error = FALSE;
   int i;
   struct fact *theFact;

   /*================================*/
   /* Get the deftemplate associated */
   /* with the fact being asserted.  */
   /*================================*/

   theExpression = GetFirstArgument();
   theDeftemplate = (struct deftemplate *) theExpression->value;

   /*=======================================*/
   /* Create the fact and store the name of */
   /* the deftemplate as the 1st field.     */
   /*=======================================*/

   if (theDeftemplate->implied == FALSE)
     {
      newFact = CreateFactBySize(theEnv,theDeftemplate->numberOfSlots);
      slotPtr = theDeftemplate->slotList;
     }
   else
     {
      newFact = CreateFactBySize(theEnv,1);
      if (theExpression->nextArg == NULL)
        {
         newFact->theProposition.theFields[0].type = MULTIFIELD;
         newFact->theProposition.theFields[0].value = CreateMultifield2(theEnv,0L);
        }
      slotPtr = NULL;
     }

   newFact->whichDeftemplate = theDeftemplate;

   /*===================================================*/
   /* Evaluate the expression associated with each slot */
   /* and store the result in the appropriate slot of   */
   /* the newly created fact.                           */
   /*===================================================*/

   EnvIncrementClearReadyLocks(theEnv);

   theField = newFact->theProposition.theFields;

   for (theExpression = theExpression->nextArg, i = 0;
        theExpression != NULL;
        theExpression = theExpression->nextArg, i++)
     {
      /*===================================================*/
      /* Evaluate the expression to be stored in the slot. */
      /*===================================================*/

      EvaluateExpression(theEnv,theExpression,&theValue);

      /*============================================================*/
      /* A multifield value can't be stored in a single field slot. */
      /*============================================================*/

      if ((slotPtr != NULL) ?
          (slotPtr->multislot == FALSE) && (theValue.type == MULTIFIELD) :
          FALSE)
        {
         MultiIntoSingleFieldSlotError(theEnv,slotPtr,theDeftemplate);
         theValue.type = SYMBOL;
         theValue.value = EnvFalseSymbol(theEnv);
         error = TRUE;
        }

      /*==============================*/
      /* Store the value in the slot. */
      /*==============================*/

      theField[i].type = theValue.type;
      theField[i].value = theValue.value;

      /*========================================*/
      /* Get the information for the next slot. */
      /*========================================*/

      if (slotPtr != NULL) slotPtr = slotPtr->next;
     }

   EnvDecrementClearReadyLocks(theEnv);

   /*============================================*/
   /* If an error occured while generating the   */
   /* fact's slot values, then abort the assert. */
   /*============================================*/

   if (error)
     {
      ReturnFact(theEnv,newFact);
      return -1;
     }

   /*================================*/
   /* Add the fact to the fact-list. */
   /*================================*/

   theFact = (struct fact *) EnvAssert(theEnv,(void *) newFact);

   /*========================================*/
   /* The asserted fact is the return value. */
   /*========================================*/

   if (theFact != NULL)
       return theFact->factIndex;
   else
       return FactExists(theEnv, newFact, HashFact(newFact))->factIndex;
}

// Copied from factcom.c
/****************************************************************/
/* AssertParse: Driver routine for parsing the assert function. */
/****************************************************************/
static struct expr *AssertParse(
    void *theEnv,
    struct expr *top,
    const char *logicalName)
{
    int error;
    struct expr *rv;
    struct token theToken;

    ReturnExpression(theEnv, top);
    SavePPBuffer(theEnv," ");
    IncrementIndentDepth(theEnv,8);
    rv = BuildRHSAssert(theEnv, logicalName, &theToken, &error, TRUE, TRUE,
                        "trace-assert command");
    if (rv != NULL && rv->type == FCALL)
        rv->value = FindFunction(theEnv, "trace-assert");
    DecrementIndentDepth(theEnv,8);
    return(rv);
}

void register_trace_func(void *theEnv) {
    EnvDefineFunction(theEnv, "trace-assert", 'i',
                      PTIEF assert_with_trace, "assert_with_trace");
    AddFunctionParser(theEnv, "trace-assert", AssertParse);
}
