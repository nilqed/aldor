#include "axlobs.h"
#include "utype.h"
#include "tposs.h"
#include "syme.h"
#include "absub.h"
#include "sefo.h"
#include "ti_sef.h"
#include "ti_bup.h"
#include "tfsat.h"

static SefoList utiStabExtra;

local TPoss utiStabLookupExport(Stab, Sefo, Symbol);
local TPoss utiStabLookup(Stab, Symbol);
local UTForm utibupExporter(Stab, Sefo);

local SymeList utibupLookupSymes(Stab stab, Sefo sefo, Symbol sym, TForm type);

void
utibupAddImportedTForm(Sefo sefo)
{
	utiStabExtra = listCons(Sefo)(sefo, utiStabExtra);
}

local TPoss
utiStabLookup(Stab stab, Symbol sym)
{
	TPoss tposs = tpossEmpty();
	SefoList sefoList = utiStabExtra;
	while (sefoList != listNil(Sefo)) {
		Sefo sefo = car(sefoList);
		sefoList = cdr(sefoList);
		
		tposs = tpossUnion(tposs, utiStabLookupExport(stab, sefo, sym));
	}

	return tposs;
}

local TPoss
utiStabLookupExport(Stab stab, Sefo sefo, Symbol sym) 
{
	SymeList exports, candidates;
	TForm tf;
	UTForm importedTf;
	UTFormList possl;

	tf = abTUnique(sefo);
	if (!tfIsMap(tf)) {
		return tpossEmpty();
	}
	
	if (!tfHasCatExport(tfMapRet(tf), sym))
		return tpossEmpty();
	
	importedTf = utibupExporter(stab, sefo);
	candidates = tfGetDomImportsById(utformTForm(importedTf), sym);

	if (candidates == listNil(Syme)) {
		return tpossEmpty();
	}

	possl = listNil(UTForm);
	while (candidates != listNil(Syme)) {
		Syme candidate = car(candidates);
		candidates = listFreeCons(Syme)(candidates);
		
		possl = listCons(UTForm)(utformNew(utformVars(importedTf),
						   symeType(candidate)),
					 possl);
	}
	return tpossFrTheUTFormList(possl);
}

UTForm
utibupExporter(Stab stab, Sefo sefo)
{
	SymeList params, cparams;
	AbSub sigma;
	AbSynList abParams;
	Sefo full;
	TForm tf, importedTf;
	
	tf = abTUnique(sefo);
	params = tfMapArgSymes(tf);
	sigma = absNew(stab);
	cparams = listNil(Syme);
	abParams = listNil(AbSyn);
	while (params != listNil(Syme)) {
		Syme param = car(params);
		Syme newSyme = symeClone(param);
		sigma = absExtend(param, abFrSyme(newSyme), sigma);
		params = cdr(params);
		cparams = listCons(Syme)(newSyme, cparams);
		abParams = listCons(AbSyn)(abFrSyme(newSyme), abParams);
	}
	full = abNewApplyL(sposNone, sefo, abParams);
	tiSefo(stab, full);
	importedTf = tfFullFrAbSyn(stab, full);

	return utformNew(cparams, tfSubst(sigma, importedTf));
}


TPoss
utibupId(Stab stab, AbSyn ab, TForm type)
{
	TPoss uposs;

	return utiStabLookup(stab, abIdSym(ab));
}

SymeList
utibupGetMeanings(Stab stab, AbSyn ab, TForm type)
{
	SefoList sefoList = utiStabExtra;
	SymeList symes = listNil(Syme);

	while (sefoList != listNil(Sefo)) {
		Sefo sefo = car(sefoList);
		sefoList = cdr(sefoList);
		
		symes = listNConcat(Syme)(symes,
					  utibupLookupSymes(stab, sefo, abIdSym(ab), type));
	}

	return symes;
}

local SymeList
utibupLookupSymes(Stab stab, Sefo sefo, Symbol sym, TForm type)
{
	TForm tf = abTUnique(sefo);
	SymeList candidates;
	SymeList symes;
	UTForm fullTf;

	fullTf = utibupExporter(stab, sefo);

	candidates = tfGetDomImportsById(utformTForm(fullTf), sym);

	if (candidates == listNil(Syme)) {
		return listNil(Syme);
	}
	
	symes = listNil(Syme);
	while (candidates != listNil(Syme)) {
		Syme candidate = car(candidates);
		UTForm stype = utformNew(utformVars(fullTf), symeType(candidate));
		USatMask result = utfSat(tfSatBupMask(), stype,
					 utformNewConstant(type));
		
		if (utfSatSucceed(result)) {
			AbSub sigma = utypeResultSigma(result->result);
			symes = listCons(Syme)(symeSubst(sigma, candidate), symes);
			absFree(sigma);
		}
		utfSatMaskFree(result);
		candidates = cdr(candidates);
	}
	
	return symes;
}
