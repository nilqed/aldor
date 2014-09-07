#ifndef UTI_BUP_H
#define UTI_BUP_H

TPoss utibupId(Stab stab, AbSyn ab, TForm type);
TPoss utibupGetMeaning(Stab stab, AbSyn ab, TForm type);
void utibupAddImportedTForm(Sefo tf);
SymeList utibupGetMeanings(Stab stab, AbSyn ab, TForm type);


#endif
