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
/* ------------------------------- util.c ----------------------------------
-- Copyright Swiss Federal Polytechnic Institute Zurich, 1993-94
--
-- Author: Manuel Bronstein
-- Date Created: 1 November 1993
-- Date Last Updated: 20 June 1994
*/

#include <stdio.h>

/* used to be able to set a breakpoint for the debugger (no name mangling)
   called only when an ASSERT or VERIFY failed */
extern long failedAssert()
{
	return 1;
}

/* readint(f) reads a binary integer from f */
/* extern long readint(FILE *f) */
extern long readint(f)
FILE *f;
{
	char s[10]; long *p, ans = 0;
	if (fread(s, sizeof(long), 1, f)) {
		p = (long *) &(s[0]);
		ans = *p;
	}
	return ans;
}

/* ltoa(n, s) prints n in decimal into s */
/* extern char *ltoa(long n, char *s) */
extern char *ltoa(n, s)
long n;
char *s;
{
	sprintf(s, "%ld", n);
	return s;
}

#include <sys/types.h>
#include <sys/time.h>
#include <sys/timeb.h>

/* returns a time-based seed for the random number generator */
long randomSeed()
{
	struct timeval tv;
	struct timezone tzp;	  /* for linux: all others accept 1 arg only */
	gettimeofday(&tv, &tzp);	/* supported by most O/S */
	return(tv.tv_usec - tv.tv_sec); /* some minimal shuffling */
}

