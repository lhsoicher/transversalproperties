/* This is a C version of my GAP function TransversalProperty.

   Leonard Soicher, 16/02/2026 */

#include <stdlib.h>
#include <stddef.h>
#include <stdio.h>
#include <stdbool.h>

/* Integer lists are stored in 1-dimensional arrays, 
   with indexing starting at 1.

   For an integer list  x,  x[0] is used to store the length of  x,
   so the list itself is  x[1],...,x[x[0]]  (but the array used to
   store  x  may be longer than  x[0]+1  integers). */

typedef int* intlist;

#define Length(x) ((x)[0]) /* for integer lists */

#define SetLength(x,length) (((x)[0])=(length)) /* for integer lists */

intlist IntList(int length) 
/* returns a new uninitialized integer list of the given length */
{
intlist L;
if(length<0)
   {
   fprintf(stderr,"\nIntList error: negative length given for a list\n");
   exit(EXIT_FAILURE);
   }
if((L=(intlist)malloc(((unsigned)(length+1))*sizeof(int)))==NULL)
   {
   fprintf(stderr,"\nIntList error: malloc failed\n"); 
   exit(EXIT_FAILURE);
   }
SetLength(L,length);
return L;
}

intlist IntListRead() 
/* Reads in and returns a new integer list from the standard input.
   First the length is read in, followed by the list elements (in order). */
{
int i,length;
intlist L;
scanf("%d",&length);
if(length<0)
   {
   fprintf(stderr,"\nIntListRead error: negative length given for a list\n");
   exit(EXIT_FAILURE);
   }
L=IntList(length);
for(i=1;i<=length;i++)
   scanf("%d",&L[i]);
return L;
}

int Binomial(int n,int k)
/* where n>=k>=0, returns the number of k-subsets of an n-set */
{
if(n<k || k<0)
   {
   fprintf(stderr,"\nBinomial error: n<k or k<0\n");
   exit(EXIT_FAILURE);
   }
if(k==0)
   return 1;
return (Binomial(n-1,k-1)*n)/k;
}

intlist *Combinations(int n,int k)
/* where n>=k>=0, returns an list in lex-order (indexed starting at 1), 
   of the k-subsets of {1,...,n} (given as lists of integers
   in increasing order) */ 
{
int i,j,jj,binom;
intlist *comb;
if(n<k || k<0)
   {
   fprintf(stderr,"\nCombinations error: n<k or k<0\n"); 
   exit(EXIT_FAILURE);
   }
binom=Binomial(n,k);
if((comb=(intlist *)malloc(((unsigned)(binom+1))*sizeof(intlist)))==NULL)
   {
   fprintf(stderr,"\nCombinations error: malloc failed\n"); 
   exit(EXIT_FAILURE);
   }
/* make the first combination */
comb[1]=IntList(k);
for(j=1;j<=k;j++)
   comb[1][j]=j;
for(i=2;i<=binom;i++)
   /* make the i-th combination */
   {
   comb[i]=IntList(k);
   for(j=k;j>=1;j--)
      {
      if(comb[i-1][j]<n-(k-j))
         {
         for(jj=1;jj<j;jj++)
            comb[i][jj]=comb[i-1][jj];
         comb[i][j]=comb[i-1][j]+1;
         for(jj=jj+1;jj<=k;jj++)
            comb[i][jj]=comb[i][jj-1]+1;
         break;
         }   
      }         
   }
return comb;
}

bool TransversalProperty(int n,int k,intlist *cosetreps,intlist adj,
                         intlist *comb,intlist A,bool *R,int newpoint)
/* Let (cosetreps,adj) represent a G-orbit of k-subsets of {1,...,n}, 
   where G is a transitive group on {1,...,n} and k>1. Thus, the 
   (k-1)-subsets extending i (in {1,...,n}) to a k-subset in the 
   represented G-orbit are those indexed in comb by the images 
   of the elements of adj under cosetreps[i].

   Let A represent an ordered k-partition [P[1],...,P[k]]
   of {1,...,n}, where A is an integer list of length n,
   such that A[i]==j means that i is in the j-th part P[j] of P.

   Let R represent a subset S of {1,...,n}, where R is a
   boolean list such that, for i=1,...,n, R[i]==true if
   i is in the subset S and R[i]==false if i is not in S.
   It is required that A[s]==k for all s in S (i.e. R represents 
   a subset contained in P[k]).

   Let newpoint be an element of {1,...,n} such that A[newpoint] < k
   (i.e newpoint is in one of P[1],...,P[k-1]).

   Furthermore, suppose that |P[1]|+...+|P[k-1]|<=((k-1)*n)/k, and 
   for every k-subset K in orb not containing newpoint,
   if the intersection of K with each of P[1],...,P[k-1]
   has size 1, then the remaining point of K is in the subset S
   represented by R.
   
   Then this boolean function returns true if for every k-partition Q of
   {1,...,n} satisfying:
     - Q[i] contains P[i] for i=1,...,k-1,
     - no element of S (represented by R) is in Q[k],
     - |Q[k]| >= n/k,
   there is a k-set in orb forming a transversal of Q.
 
   Otherwise, this function returns false. */
{
bool injective,tp;
bool *Rnew;
bool *covered;
int Acount,Rnewcount,i,j,kpoint,r,part;
intlist cosetrep;
intlist c;
if((Rnew=(bool *)malloc(((unsigned)(n+1))*sizeof(bool)))==NULL)
   {
   fprintf(stderr,"\nTransversalProperty error: malloc failed\n"); 
   exit(EXIT_FAILURE);
   }
if((covered=(bool *)malloc(((unsigned)(k+1))*sizeof(bool)))==NULL)
   {
   fprintf(stderr,"\nTransversalProperty error: malloc failed\n"); 
   exit(EXIT_FAILURE);
   }
Acount=0;
Rnewcount=0;
for(i=1;i<=n;i++)
   {
   if(A[i]<k)
      Acount++;
   Rnew[i]=R[i];
   if(Rnew[i])
      Rnewcount++;
   }
cosetrep=cosetreps[newpoint]; /* an element of G (in image form) 
                                 mapping 1 to newpoint */
for(i=1;i<=Length(adj);i++)
   {
   c=comb[adj[i]];
   /* first, determine if the values of A (the parts) indexed by
      newpoint and the points in the cosetrep-image of c are
      all of {1,...,k}, and if so, set kpoint to be that point in 
      this image with A[kpoint]==k  */
   injective=true;  /* initially */
   for(j=1;j<=k;j++)
      covered[j]=false;
   covered[A[newpoint]]=true;
   if(A[newpoint]==k)
      kpoint=newpoint;
   for(j=1;j<=k-1;j++)
      {
      part=A[cosetrep[c[j]]];
      if(covered[part])
         {
         /* part is covered twice */
         injective=false;
         break;
         }
      else
         {
         covered[part]=true;
         if(part==k)
            kpoint=cosetrep[c[j]];
         }
      }
   if(injective)
      {
      /* is kpoint in the set represented by Rnew? */
      if(!Rnew[kpoint])
         {
         Rnew[kpoint]=true;
         Rnewcount++;
         if((Acount+Rnewcount)*k>(k-1)*n)
            {
            free(covered);
            free(Rnew);
            return true;
            }
         }
      }
   }
if(Rnewcount==0)
   {
   free(covered);
   free(Rnew);
   return false;
   }
for(i=1;i<=n;i++)
   if(Rnew[i])
      {
      r=i;
      /* remove r from the set represented by Rnew */
      Rnew[r]=false;
      Rnewcount--;
      break;
      }
/* now try putting r in each of the first k-1 parts of the 
   ordered partition represented by A */
for(i=1;i<=k-1;i++)
   {
   A[r]=i;
   tp=TransversalProperty(n,k,cosetreps,adj,comb,A,Rnew,r);
   if(!tp)
      {
      free(covered);
      free(Rnew);
      return false;
      }
   A[r]=k;
   }
free(covered);
free(Rnew);
return true;
}

int main(int argc, char *argv[])
{  
int n,k,i;
bool result;
intlist adj; /* the adjacency of vertex 1 in orbgraph (the graph encoding
                the G-orbit on k-sets currently under consideration),
                where G is a transitive permutation group */
intlist *cosetreps; /* representatives for the right cosets in G of the
                       stabilizer in G of 1 */ 
intlist *comb; /* list of integer lists (in lex-order) of the 
                  (k-1)-subsets of {1,...n}, indexed from 1 */
intlist shortrep; 
intlist A; /* an integer list representing a partition of {1,...,n}:
              A[i]==j means that i is in the the j-th part  */
bool *R; /* a boolean list representing a subset of {1,...,n}, so
            for i=1,...,n, R[i]==true means that i is in the subset 
            and R[i]==false means that i is not in the subset */
scanf("%d %d",&n,&k);
if((k<2) || (k>n))
   {
   fprintf(stderr,"\nbad input: must have 2<=k<=n\n");
   exit(EXIT_FAILURE);
   }
/* read in cosetreps */
if((cosetreps=(intlist *)malloc(((unsigned)(n+1))*sizeof(intlist)))==NULL)
   {
   fprintf(stderr,"\nmaking cosetreps error: malloc failed\n"); 
   exit(EXIT_FAILURE);
   }
for(i=1;i<=n;i++)
   cosetreps[i]=IntListRead();
adj=IntListRead();
comb=Combinations(n,k-1); 
A=IntList(n);
if((R=(bool *)malloc(((unsigned)(n+1))*sizeof(bool)))==NULL)
   {
   fprintf(stderr,"\nmain error: malloc failed\n"); 
   exit(EXIT_FAILURE);
   }
result=true;  /* initially */
while(Length(shortrep=IntListRead())!=0)
   {
   for(i=1;i<=n;i++)
      {
      A[i]=k;
      R[i]=false;
      }
   for(i=1;i<=Length(shortrep);i++)
      A[shortrep[i]]=i;
   result=TransversalProperty(n,k,cosetreps,adj,comb,A,R,shortrep[1]);
   if(!result)
      /* k-set orbit defined by orbgraph does not provide a witness for k-et */
      break;
   }
printf("%d\n",result);
exit(EXIT_SUCCESS);
}
