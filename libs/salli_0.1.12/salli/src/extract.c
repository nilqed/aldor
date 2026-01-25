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
/****************************** extract.c ******************************

   Author: Manuel Bronstein
   Date Last Updated: 8 December 1999

   extract simply extracts from any file all the lines contained between
   #if MARKER and #endif, where MARKER is the specified marker.

   Flags recognized:
    -h      (help)
    -m name (marker)  use name as start marker (default AUTODOC)
    -o name (output)  use name as output file name
    -r      (reverse) removes all the lines between the markers
    -t      (test)    make a stand-alone LaTeX file for testing, by adding
                      the appropriate preamble and conclusion
    -v      (verbose)
*/

#include <stdio.h>
#include <string.h>
#include "flags.h"

#define MAXLINE 500
#define	STARTDOC "#if "
#define	ENDDOC   "#endif"
#define	AUTODOC  "AUTODOC"
#define	ASEXT    ".as"
#define	TEXEXT   ".tex"
#define	EXTCHAR	 '.'

#define	HELPFLAG 'h'
#define	MARKFLAG 'm'
#define	OUTFLAG	 'o'
#define	REVFLAG	 'r'
#define	TESTFLAG 't'
#define	VERBFLAG 'v'

static banner()
{
	fputs("Documentation extractor 1.1 - (c) Manuel Bronstein 1995-98\n",
		stderr);
}

static int help()
{
	banner();
	fputs("Usage: extract [-opts] file[.as]\n\n", stderr);
	fputs("  -h      show this help\n", stderr);
	fputs("  -v      verbose (show progress)\n", stderr);
	fputs("  -t      test (produce stand-alone latex file)\n", stderr);
	fputs("  -o name  use name for the output tex file\n", stderr);
	fputs("  -m name  use name for the marker to select\n", stderr);
	fputs("  -r      reverse (keep the code lines, strip the doc)\n\n",
									stderr);
	return 0;
}

/* Returns the new value of doc */
static int stripdoc(FILE *fp, char *s, char *start, int doc, int non, int noff,
			int verbose, int reverse, int *page)
{
	if (doc) {
		if (!strncmp(s, ENDDOC, noff)) {
			if (verbose) fputc(']', stderr);
			doc = 0;
		}
		else if (!reverse) fputs(s, fp);
	}
	else {
		if (!strncmp(s, start, non)) {
			if (verbose) fprintf(stderr, "[%d", ++*page);
			++doc;
		}
		else if (reverse) fputs(s, fp);
	}
	return doc;
}

/* removes an extension if any */
static killExtension(char *s)
{
	while (*s && (*s != EXTCHAR)) s++;
	if (*s == EXTCHAR) *s = '\0';
}

/* returns 1 if s has an extension, 0 otherwise */
static int hasExtension(char *s)
{
	while (*s && (*s != EXTCHAR)) s++;
	return(*s == EXTCHAR);
}

/* returns 0 if ok, > 0 if error */
static int getFiles(int argc, char **argv, FILE **fpin, FILE **fpout, int strip)
{
	int out, err = 0;
	char *name, s[MAXLINE], t[MAXLINE];

	name = getFlagName(argc, argv, OUTFLAG);
	out = name != NULL;
	if (out) strcpy(t, name);
	name = (char *) argv[argc - 1];
	if ((argc == 0) || (*name == '-') || (out && !strcmp(t, name))) {
		fputs("extract: no file name given\n", stderr);
		err = 1;
	}
	else {
		strcpy(s, name);
		if (!hasExtension(s)) strcat(s, ASEXT);
		if (!out) {
			strcpy(t, s);
			killExtension(t);
			strcat(t, TEXEXT);
		}
		*fpin = fopen(s, "r");
		if (*fpin == NULL) {
			fputs("extract: cannot open ", stderr);
			fputs(s, stderr);
			fputs("\n", stderr);
			err = 2;
		}
		else {
			*fpout = (strip && !out) ? stdout : fopen(t, "w");
			if (*fpout == NULL) {
				fclose(*fpin);
				fputs("extract: cannot create ", stderr);
				fputs(t, stderr);
				fputs("\n", stderr);
				err = 3;
			}
		}
	}
	return err;
}

static preamble(FILE *fp)
{
	fputs("\\documentclass[12pt]{asdoc}\n", fp);
	fputs("\\pagestyle{fancyplain}\n", fp);
	fputs("\\begin{document}\n", fp);
}

static closing(FILE *fp)
{
	fputs("\\end{document}\n", fp);
}

/* returns 0 if ok, error code otherwise */
static int extract(int argc, char **argv)
{
	int strip, verbose, test, err, non, noff, doc = 0, cont = 1, page = 0;
	char *marker, s[MAXLINE], t[MAXLINE], start[MAXLINE];
	FILE *fpin, *fpout;

	verbose = existFlag(argc, argv, VERBFLAG);
	if (verbose) banner();
	err = getFiles(argc, argv, &fpin, &fpout,
			strip = existFlag(argc, argv, REVFLAG));
	if (err) return err;
	strcpy(start, STARTDOC);
	marker = getFlagName(argc, argv, MARKFLAG);
	strcat(start, marker == NULL ? AUTODOC : marker);
	non = strlen(start);
	noff = strlen(ENDDOC);
	test = (!strip) && existFlag(argc, argv, TESTFLAG);
	if (test) preamble(fpout);
	while (fgets(s, MAXLINE, fpin) != NULL)
		doc = stripdoc(fpout,s,start,doc,non,noff,verbose,strip,&page);
	if (test) closing(fpout);
	if (verbose) fputc('\n', stderr);
	fclose(fpin);
	fclose(fpout);
	return 0;
}

main(int argc, char **argv)
{
	exit(existFlag(argc, argv, HELPFLAG) ? help() : extract(argc, argv));
}
