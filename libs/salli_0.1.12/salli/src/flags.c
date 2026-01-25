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
/****************************** flags.c ******************************

   Author: Manuel Bronstein
   Date Last Updated: 17 February 1995

   Utilities to treat command line flags.
*/


#include <stdio.h>
#include "flags.h"

/* char preceding a flag */
#define FLAG_SIGNAL	'-'

/* flags which are followed by a string argument */
#define	STRINGFLAGS	"lfoIL"

static int member(char c, char *s)
{
	while (*s) if (*(s++) == c) return 1;
	return 0;
}

static int getfl(char *s, char c)
{
	int stop, cont = *s;
	while (cont) {
		stop = member(*s, STRINGFLAGS);
		if (*(s++) == c) return(atoi(s));
		cont = *s && !stop;
	}
	return(-1);
}

static char *getflname(char *s, char c)
{
	int stop, cont = *s;
	while (*s) {
		stop = member(*s, STRINGFLAGS);
		if (*(s++) == c) return s;
		cont = *s && !stop;
	}
	return NULL;
}

/* Returns the numerical value of a flag, or -1 if not there */
int getFlag(int ac, char **ag, char flag)
{
	int i, val;
	for (i = 1; i < ac; i++)
	    if ((ag[i][0] == FLAG_SIGNAL)
		 && ((val = getfl(ag[i], flag))) >= 0)
			return val;
	return(-1);
}

/* Returns the string value of a flag, or NULL if not there */
char *getFlagName(int ac, char **ag, char flag)
{
	int i;
	char *s;
	for (i = 1; i < ac; i++)
	    if ((ag[i][0] == FLAG_SIGNAL)
		&& ((s = getflname(ag[i], flag)) != NULL))
			return((*s || (i == ac)) ? s : ag[++i]);
	return NULL;
}

/* Returns the pos-th non-flag string argument */
char *getNthArgument(int ac, char **ag, int pos)
{ int i, count = 0;

	for (i = 1; i < ac; i++)
	    if ((ag[i][0] != FLAG_SIGNAL) && (++count == pos))
		return(ag[i]);
	return NULL;
}

