#include "utype.h"
#include "sefo.h"
#include "tform.h"
#include "tfsat.h"
#include "absyn.h"
#include "debug.h"
#include "store.h"
#include "format.h"
#include "ablogic.h"
#include "absub.h"
#include "stab.h"
#include "util.h"

Bool utypeDebug = false;
#define utypeDEBUG			DEBUG_IF(utype)		afprintf

CREATE_LIST(UTForm);

/*
 import from List;
 
 list(list(2)) -->
    2 --> Integer
    list --> ? -> List ?
    list --> ? -> List ?

    unify(?, Integer) --> ? == Integer
    
  MapOperations(T: with, L: ListType T): with
      map: (L, T -> T) -> L

  MapOperations2(T: with, X: with, L: ListType T, M: ListType X): with
      map: (L, T -> X) -> M

  map([1,2,3], f)

  f:  Integer -> Integer
  [1,2,3]: List Integer

  map: [T, L] (L, T->T) -> L

  map([1,2,3], f)
    ->> [T, L] (L, T -> T)... (List Integer, Integer -> Integer)
    ->> (List Integer, Integer -> Integer)
    : List Integer

*/


static struct utypeResult empty = { listNil(Syme), listNil(Sefo) };

/* Local */
local UTypeResult utypeResultExtend(UTypeResult result, Syme symeToAdd, Sefo sefoToAdd);
local UTypeResult utypeUnifySefo(UType ut1, UType ut2, Sefo sefo1, Sefo sefo2);
local UTypeResult utypeUnifyId(UType ut1, UType ut2, Syme syme1, Sefo sefo2);

UTForm
utformNew(SymeList freevars, TForm tform)
{
	UTForm utform = (UTForm) stoAlloc(OB_Other, sizeof(*utform));
	utform->tf = tform;
	utform->vars = freevars;
	utform->typeInfo = ablogFalse();
	return utform;
}

void
utformFree(UTForm utform)
{
	tfFree(utform->tf);
	listFree(Syme)(utform->vars);
	ablogFree(utform->typeInfo);
}

TForm
utformConstOrFail(UTForm utform)
{
	if (utformIsConst(utform))
		return utform->tf;
	else
		bug("Expected a constant type form here");
	return 0;
}

Bool
utformIsConst(UTForm utform)
{
	return utform->vars == listNil(Syme);
}

UTForm
utformNewConstant(TForm tf)
{
	return utformNew(listNil(Syme), tf);
}

TForm
utformTForm(UTForm utf)
{
	return utf->tf;
}

UTForm
utformFollowOnly(UTForm utf)
{
	TForm tf = utf->tf;
	tf = tfFollowOnly(tf);
	if (tf != utf->tf)
		return utformNew(listCopy(Syme)(utf->vars), tf);
	return utf;
}

Bool
utfIsUnknown(UTForm utf)
{
	return tfIsUnknown(utf->tf);
}

Bool
utfIsConstant(UTForm utf)
{
	return utf->vars == listNil(Syme);
}

UTForm
utfDefineeType(UTForm utf)
{
	return utformNew(listCopy(Syme)(utformVars(utf)),
			 tfDefineeType(utformTForm(utf)));
}

Syme
utfDefineeSyme(UTForm utf)
{
	return tfDefineeSyme(utformTForm(utf));
}

Bool
utformIsAnyMap(UTForm utf)
{
	if (tfIsAnyMap(utformTForm(utf)))
		return true;

	if (!tfIsId(utformTForm(utf)))
		return false;
	/* "Ax, x" could be a map, but let's not worry about that yet */
	return false;
}

UTForm
utfMapRet(UTForm utf)
{
	return utformNew(listCopy(Syme)(utformVars(utf)),
			 tfMapRet(utformTForm(utf)));
}

UTForm
utfMapArg(UTForm utf)
{
	return utformNew(listCopy(Syme)(utformVars(utf)),
			 tfMapArg(utformTForm(utf)));
}

Bool
utfIsMulti(UTForm utf)
{
	return tfIsMulti(utformTForm(utf));
}


SymeList
utformVars(UTForm utf)
{
	return utf->vars;
}

int
utformPrint(FILE *file, UTForm utf)
{
	if (utfIsConstant(utf))
		return tfPrint(file, utformTForm(utf));
	else
		return afprintf(file, "<ForAll %pSymeList: %pTForm>", utf->vars, utf->tf);
}

Bool
utfSatisfies(UTForm utfS, UTForm utfT)
{
	return tfSatisfies(utformConstOrFail(utfS), utformConstOrFail(utfT));
}

Bool
utformEqual(UTForm utf1, UTForm utf2)
{
	return tfEqual(utformConstOrFail(utf1),
		       utformConstOrFail(utf2));
}

UTForm
utformSubst(AbSub sigma, UTForm utf)
{
	return utformNew(utformVars(utf), tformSubst(sigma, utformTForm(utf)));
}

UTForm
utfAsMultiArgN(UTForm utf, Length argc, Length n)
{
	return utformNew(utformVars(utf),
			 tfAsMultiArgN(utformTForm(utf), argc, n));
}

AbSyn
utfAsMultiSelectArg(AbSyn ab, Length argc, Length n, AbSynGetter argf,
		    UTForm utfi, Bool * def, Length * pos)
{
	return tfAsMultiSelectArg(ab, argc, n, argf, utformTForm(utfi), def, pos);
}

Bool
utfIsPending(UTForm utf)
{
	return tfIsPending(utformTForm(utf));
}

UType
utfExpr(UTForm utf)
{
	return utypeNew(listCopy(Syme)(utformVars(utf)), tfExpr(utformTForm(utf)));
}


UTypeResult
utformUnify(UTForm ut1, UTForm ut2)
{
	return utypeUnify(utfExpr(ut1), utfExpr(ut2));
}


UType
utypeNew(SymeList freevars, Sefo sefo)
{
	UType utype = (UType) stoAlloc(OB_Other, sizeof(*utype));
	utype->sefo = sefo;
	utype->vars = freevars;
	utype->typeInfo = ablogFalse();
	return utype;
}

SymeList
utypeVars(UType utype)
{
	return utype->vars;
}

Sefo
utypeSefo(UType utype)
{
	return utype->sefo;
}

Bool
utypeHasVar(UType utype, Syme syme)
{
	return listMember(Syme)(utype->vars, syme, symeEqual);
}

Bool
utypeIsConstant(UType utype)
{
	return utype->vars == listNil(Syme);
}

UType
utypeNewConstant(Sefo sefo)
{
	return utypeNew(listNil(Syme), sefo);
}

UType
utypeNewVar(Syme syme)
{
	return utypeNew(listSingleton(Syme)(syme), abFrSyme(syme));
}

UTypeResult 
utypeResultFailed()
{
	return NULL;
}

UTypeResult
utypeResultEmpty() 
{
	return &empty;
}

Bool
utypeResultIsFail(UTypeResult res)
{
	return res == NULL;
}

Bool
utypeResultIsEmpty(UTypeResult res)
{
	if (utypeResultIsFail(res))
		return false;
	
	return res->symes == listNil(Syme);
}

UTypeResult
utypeResultNew()
{
	UTypeResult res = (UTypeResult) stoAlloc(OB_Other, sizeof(*res));
	res->symes = listNil(Syme);
	res->sefos = listNil(Sefo);
	return res;
}

UTypeResult
utypeResultOne(Syme syme, Sefo sefo)
{
	UTypeResult res = utypeResultNew();
	res->symes = listSingleton(Syme)(syme);
	res->sefos = listSingleton(Sefo)(sefo);

	return res;
}

UTypeResult
utypeResultTwo(Syme syme1, Sefo sefo1, Syme syme2, Sefo sefo2)
{
	UTypeResult res = utypeResultNew();
	res->symes = listList(Syme)(2, syme1, syme2);
	res->sefos = listList(Sefo)(2, sefo1, sefo2);

	return res;
}

void
utypeResultFree(UTypeResult result)
{
	if (utypeResultIsFail(result)) {
		return;
	}
	if (result == &empty) {
		return;
	}
	listFree(Syme)(result->symes);
	/*listFreeDeeply(Sefo)(result->sefos, abFree);*/
	stoFree(result);
}

int
utypeResultPrint(FILE *fout, UTypeResult utypeResult)
{
	struct ostream ostream;
	int n;

	ostreamInitFrFile(&ostream, fout);
	n = utypeResultOStreamPrint(&ostream, utypeResult);
	ostreamClose(&ostream);

	return n;
}

int
utypeResultOStreamPrint(OStream ostream, UTypeResult utypeResult)
{
	SymeList symeList;
	SefoList sefoList;
	String sep = "";
	int acc = 0;

	if (utypeResultIsFail(utypeResult))
		return ostreamPrintf(ostream, "[UTR: Fail]");
	acc += ostreamPrintf(ostream, "[UTR: ");
	symeList = utypeResult->symes;
	sefoList = utypeResult->sefos;

	while (symeList != listNil(Syme)) {
		Syme syme = car(symeList);
		Sefo sefo = car(sefoList);
		acc += ostreamPrintf(ostream, "%s%pSyme --> %pSefo", sep, syme, sefo);
		sep = ", ";
		symeList = cdr(symeList);
		sefoList = cdr(sefoList);
	}
	acc += ostreamPrintf(ostream, "]");
	return acc;
}


UTypeResult
utypeUnify(UType ut1, UType ut2)
{	return utypeUnifySefo(ut1, ut2, ut1->sefo, ut2->sefo);
}

/* NB: Destructive in both res1 and res2 */
UTypeResult
utypeResultMerge(UTypeResult res1, UTypeResult res2) 
{
	SymeList symeList2;
	SefoList sefoList2;
	if (utypeResultIsFail(res1) || utypeResultIsFail(res2))
		return utypeResultFailed();
	if (utypeResultIsEmpty(res1))
		return res2;
	if (utypeResultIsEmpty(res2))
		return res2;
	afprintf(dbOut, "Unify: %pSymeList %pSymeList\n", res1->symes, res2->symes);
	symeList2 = res2->symes;
	sefoList2 = res2->sefos;
	while (symeList2 != listNil(Syme)) {
		UTypeResult nextResult;
		Syme syme = car(symeList2);
		Sefo sefo = car(sefoList2);
		res1 = utypeResultExtend(res1, syme, sefo);
		if (utypeResultIsFail(res1)) {
			utypeResultFree(res2);
			return res1;
		}
		symeList2 = cdr(symeList2);
		sefoList2 = cdr(sefoList2);
		
	}
	utypeResultFree(res2);
	return res1;
}

local UTypeResult
utypeResultExtend(UTypeResult result, Syme symeToAdd, Sefo sefoToAdd)
{
	SymeList symeList = result->symes;
	SefoList sefoList = result->sefos;
	
	while (symeList != listNil(Syme)) {
		Syme syme = car(symeList);
		Sefo sefo = car(sefoList);
		symeList = cdr(symeList);
		sefoList = cdr(sefoList);

		if (symeEqual(symeToAdd, syme)) {
			afprintf(dbOut, "Want to merge %pSyme ++ %pSefo ++ %pSefo ++\n",
				 symeToAdd, sefo, sefoToAdd);
			if (sefoEqual(sefo, sefoToAdd))
				continue;
			utypeResultFree(result);
			return utypeResultFailed();
		}
	}
	result->symes = listCons(Syme)(symeToAdd, result->symes);
	result->sefos = listCons(Sefo)(sefoToAdd, result->sefos);
	return result;
}


local UTypeResult
utypeUnifySefo(UType ut1, UType ut2, Sefo sefo1, Sefo sefo2) 
{
	UTypeResult result;
 	int i;
	utypeDEBUG(dbOut, "Unify: %pAbSyn %pAbSyn\n", sefo1, sefo2);

	if (!(abIsId(sefo1) && utypeHasVar(ut1, abSyme(sefo1)))
	    && abIsId(sefo2) && utypeHasVar(ut2, abSyme(sefo2)))
		return utypeUnifySefo(ut2, ut1, sefo2, sefo1);
	if (abIsId(sefo1) && utypeHasVar(ut1, abSyme(sefo1))) {
		return utypeUnifyId(ut1, ut2, abSyme(sefo1), sefo2);
	}
	if (abIsId(sefo1)) {
		if (sefoEqual(sefo1, sefo2)) 
			return utypeResultEmpty();
		else
			return utypeResultFailed();
	}
	if (abTag(sefo1) != abTag(sefo2)) {
		return utypeResultFailed();
	}
	if (abArgc(sefo1) != abArgc(sefo2)) {
		return utypeResultFailed();
	}

	result = utypeResultEmpty();
	for (i=0; i<abArgc(sefo1); i++) {
		UTypeResult utrI = utypeUnifySefo(ut1, ut2, abArgv(sefo1)[i], abArgv(sefo2)[i]);
		result = utypeResultMerge(result, utrI);
	}
	return result;
}

local UTypeResult
utypeUnifyId(UType ut1, UType ut2, Syme syme1, Sefo sefo2)
{
	assert(utypeHasVar(ut1, syme1));
	if (abIsId(sefo2) && utypeHasVar(ut2, abSyme(sefo2))) {
		Syme syme3 = symeClone(syme1);
		afprintf(dbOut, "UnifyId: %pSyme %pSefo\n", syme1, sefo2);
		return utypeResultTwo(syme1, abFrSyme(syme3),
				      abSyme(sefo2), abFrSyme(syme3));
	}
	else {
		return utypeResultOne(syme1, sefo2);
	}
}

UType
utypeResultApply(UTypeResult result, UType utype)
{
	SymeList freevars;
	AbSub sigma;
	SymeList symes;
	assert(!utypeResultIsFail(result));

	if (utypeIsConstant(utype))
		return utype;

	sigma = utypeResultSigma(result);

	freevars = listNil(Syme);
	symes = utypeVars(utype);

	while (symes != listNil(Syme)) {
		if (!listMemq(Syme)(result->symes, car(symes)))
			freevars = listCons(Syme)(car(symes), freevars);
		symes = cdr(symes);
	}

	return utypeNew(freevars, sefoSubst(sigma, utypeSefo(utype)));
}

AbSub
utypeResultSigma(UTypeResult result)
{
	AbSub sigma;
	SymeList symes;
	SefoList sefos;

	sigma = absNew(stabFile());
	symes = result->symes;
	sefos = result->sefos;
	while (symes != listNil(Syme)) {
		Syme syme = car(symes);
		Sefo sefo = car(sefos);
		symes = cdr(symes);
		sefos = cdr(sefos);

		sigma = absExtend(syme, sefo, sigma);
	}

	return sigma;
}

UTForm
utformFromType(UType type)
{
	return utformNew(listCopy(Syme)(utypeVars(type)),
			 tfFullFrAbSyn(stabFile(), utypeSefo(type)));
}


UTForm
utypeResultApplyTForm(UTypeResult result, UTForm utf)
{
	UType usefo = utypeResultApply(result, utfExpr(utf));

	return utformFromType(usefo);
}


