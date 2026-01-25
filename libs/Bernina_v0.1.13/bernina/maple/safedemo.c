/*
 * ======================================================================
 * This code was written all or part by Dr. Manuel Bronstein from
 * Inria-CAFE project team. After his sudden death on June 6, 2005, Inria
 * decided to publish this code under the CeCILL open source license in
 * memory of Dr. Manuel Bronstein.
 * 
 * This software is governed by the CeCILL license under French law and
 * abiding by the rules of distribution of free software. You can use,
 * modify and/or redistribute the software under the terms of the CeCILL
 * license as circulated by CEA, CNRS and Inria at the following URL :
 * http://www.cecill.info/licences/Licence_CeCILL_V2-en.html
 * 
 * As a counterpart to the access to the source code and rights to copy,
 * modify and redistribute granted by the license, users are provided
 * only with a limited warranty and the software's author, the holder of
 * the economic rights, and the successive licensors have only limited
 * liability.
 * 
 * In this respect, the user's attention is drawn to the risks associated
 * with loading, using, modifying and/or developing or reproducing the
 * software by the user in light of its specific status of free software,
 * that may mean that it is complicated to manipulate, and that also
 * therefore means that it is reserved for developers and experienced
 * professionals having in-depth computer knowledge. Users are therefore
 * encouraged to load and test the software's suitability as regards
 * their requirements in conditions enabling the security of their
 * systems and/or data to be ensured and, more generally, to use and
 * operate it in the same conditions as regards security.
 * 
 * The fact that you are presently reading this means that you have had
 * knowledge of the CeCILL license and that you accept its terms.
 * ======================================================================
 * 
 */
#include <stdio.h>
#include <stdlib.h>

static char getnextchar(char x)
{
	int space = 1;
	char ch = 'x';
	while (space && (ch != EOF)) {
		ch = (char) getchar();
		space = isspace(ch);
	}
	if ((x != '\0') && isalpha(ch) && (ch != x)) {
		printf("bernina demo: symbol '%c' not allowed\n", ch);
		exit(1);
	}
	return ch;
}

static void getnextcoeff(char x, FILE *fp)
{
	char ch = getnextchar(x);
	if (ch == '|') putc('0', fp);
	else while (ch != '|') {
		putc(ch, fp);
		ch = getnextchar(x);
	}
}

main()
{
	FILE *fpin;
	char inname[100], cmd[200], ch, x;

	/* get independent variable, followed by separator '|' */
	x = getnextchar('\0');
	if (x == EOF) {
		printf("bernina demo: no input!\n");
		exit(1);
	}
	ch = getnextchar('\0');
	if (ch != '|') {
		printf("bernina demo: independent variable must be one character long\n");
		exit(1);
	}

	/* prepare maple input file */
	strcpy(inname, "/tmp/bdemo_inXXXXXX");
	if (mkstemp(inname) == -1) {
		printf("bernina demo: cannot create temporary file\n");
		exit(1);
	}
	fpin = fopen(inname, "w");
	if (fpin == NULL) {
		printf("bernina demo: cannot open %s\n", inname);
		exit(1);
	}
        fprintf(fpin, "with(Order3):\n");
        fprintf(fpin, "dsolve3((");

	/* get coefficients of D^3, D^2, D, 1, separated by '|'  */
	getnextcoeff(x, fpin);			/* coeff of D^3 */
        fprintf(fpin, ")*D^3+(");
	getnextcoeff(x, fpin);			/* coeff of D^2 */
        fprintf(fpin, ")*D^2+(");
	getnextcoeff(x, fpin);			/* coeff of D */
        fprintf(fpin, ")*D+(");
	getnextcoeff(x, fpin);			/* coeff of 1 */
        fprintf(fpin, "), D, %c,", x);
	getnextcoeff(x, fpin);			/* 0 or 1 (for group) */
        fprintf(fpin, ");\n if 1=");
	getnextcoeff(x, fpin);			/* 0 or 1 (for lprint) */
        fprintf(fpin, " then print(); lprint(%%); fi;\nquit;\n");
	fclose(fpin);

	sprintf(cmd, "maple6 -q < %s", inname);
	if (system(cmd) == 0) unlink(inname);
}

