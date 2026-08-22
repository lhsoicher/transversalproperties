#
# Leonard Soicher, 30 July 2026.
#
# This file contains functions to determine the properties k-et, k-ut,
# strong k-ut, and k-id of given (finite degree) permutation groups.
#
# To use these functions, first compile the program `tpexternal.c'
# (if you want to make use of this external program which can greatly
# speed up the computation of the k-ut and k-et properties).
#
# Then set the default info level here to 0, 1, 2 or 3 as desired,
# to determine how much extra information will be printed out.
#
DeclareInfoClass("TRANSVERSALPROPERTIES_info");
SetInfoLevel(TRANSVERSALPROPERTIES_info,2);

TRANSVERSALPROPERTIES_tpexternal_maxnum:=1;
# Set this global variable to 0 if you do *not* want to make use of
# the external C program `tpexternal.c'.
# 
# If you *do* want to make use of the external program
# (which can greatly speed up the computation of k-ut and k-et),
# then this global variable should be set to the maximum number
# of "shortreps" to be handled by the external program for each "rep"
# when computing k-ut or k-et. Usually, the value 1 is best.

TRANSVERSALPROPERTIES_tpexternal_exe:="/home/lsoicher/bin/tpexternal";
# If you are using the external program `tpexternal.c', then you should
# set this variable to the program's executable file.

# Then in a GAP session, use the `Read' command to read in this 
# file `transversalproperties.g', and you should be ready to go!

# Normally, the global variables below should not be changed.

TRANSVERSALPROPERTIES_tmpdir:=DirectoryTemporary();
# This is for files to communicate with the external program's
# executable file. 

TRANSVERSALPROPERTIES_testmode:=false;
# Normally this global variable should be set to `false',
# but if set to `true' then certain theoretical shortcuts are *not* 
# taken, in order to further test the main code.

LoadPackage("grape");

PrintStreamTpexternalInput:=function(stream,G,k,orbgraph,shortreps)
#
# Prints the input data for tpexternal on the given output stream. 
#
local n,i,j,adj,cosetreps,rt;
n:=LargestMovedPoint(G);
rt:=RightTransversal(G,Stabilizer(G,1));
cosetreps:=[];
for i in [1..n] do
   cosetreps[1^rt[i]]:=rt[i]; 
od;
# so, for j=1,...,n, cosetreps[j] maps 1 to j
PrintTo(stream,n," ",k);
for i in [1..n] do 
   AppendTo(stream,"\n",n,"\n"); 
   for j in [1..n] do 
      AppendTo(stream,j^cosetreps[i]," ");
   od;
od;
adj:=Adjacency(orbgraph,1);
AppendTo(stream,"\n",Length(adj),"\n"); 
for i in adj do 
   AppendTo(stream,i-n," ");
od;
for i in [1..Length(shortreps)] do
   AppendTo(stream,"\n",Length(shortreps[i]),"\n");
   for j in shortreps[i] do 
      AppendTo(stream,j," ");
   od;
od;
AppendTo(stream,"\n",0,"\n"); # end of data
end;

LeastSetRepresentatives := function(G,k)
#
# Suppose  G  is a permutation group on  [1..n],
# where  n:=LargestMovedPoint(G),  and  k  is a 
# non-negative integer <= n. 
# 
# Then this function returns the set of lex-least 
# representatives for the orbits of  G  on the
# k-subsets  of  [1..n].
#
if not (IsPermGroup(G) and IsInt(k)) then
   Error("usage: LeastSetRepresentatives( <PermGrp>, <Int> )");
elif k<0 or k>LargestMovedPoint(G) then
   Error("must have  0 <= <k> <= LargestMovedPoint(<G>)");
fi;
return Set(CompleteSubgraphs(CompleteGraph(G),k,2),x->SmallestImageSet(G,x));
end;

IsSetTransitive := function(G,k)
#
# Suppose  G  is a permutation group on  [1..n],
# where  n:=LargestMovedPoint(G),  and  k  is a 
# non-negative integer <= n.
# 
# Then this boolean function returns  true  if  G  is transitive
# in its natural action on the k-subsets of [1..n], 
# and  false  if not.
#
local n;
if not (IsPermGroup(G) and IsInt(k)) then
   Error("usage: IsSetTransitive( <PermGrp>, <Int> )");
fi;
n:=LargestMovedPoint(G);
if k<0 or k>n then
   Error("must have  0 <= <k> <= LargestMovedPoint(<G>)");
fi;
if k=0 or k=n then
   return true;
fi;
if k>n/2 then
   k:=n-k;
fi;
if Transitivity(G,[1..n])>=k then
   return true;
fi;
return Length(CompleteSubgraphs(CompleteGraph(G),k,2))=1;
end;

OrbGraph := function(G,rep)
#
# Suppose  G  is a permutation group on  [1..n],
# where  n:=LargestMovedPoint(G), and  rep  is a 
# k-subset  of  [1..n],  with  k>0. 
# 
# Then this function returns a graph whose vertices
# (actually vertex-names) consist of the concatenation
# of  [1..n]  with the set of (k-1)-subsets of  [1..n]. 
# The edges consist of the ordered pairs  [x,y]  
# such that  x  is in  [1..n],  y   is a  (k-1)-subset
# of  [1..n],  and  {x} union y  is a  k-subset  in the 
# G-orbit  of  rep. 
#
local n,k,leastrep;
if not (IsPermGroup(G) and IsSet(rep)) then
   Error("usage: OrbGraph( <PermGrp>, <Set> )");
fi;
n:=LargestMovedPoint(G);
k:=Length(rep);
if not (k>0 and IsSubset([1..n],rep)) then
   Error("<rep> must be a non-empty subset of [1..LargestMovedPoint(<G>)]");
fi;
leastrep:=SmallestImageSet(G,rep);
return Graph(G,Concatenation([1..n],Combinations([1..n],k-1)),
   function(x,g)
   if IsInt(x) then
      return OnPoints(x,g);
   else
      return OnSets(x,g);
   fi;
   end,
   function(x,y) 
   if not (IsInt(x) and IsList(y)) then
      return false;
   fi;
   return not (x in y) and SmallestImageSet(G,Union(y,[x]))=leastrep;
   end,
   true);
end;

TransversalProperty := function(G,k,orbgraph,A,R,newpoint,done)
#
# Suppose  orbgraph  represents a  G-orbit  of  k-subsets  of  [1..n],
# such that  n:=LargestMovedPoint(G)  and   2 <= k <= n.
# 
# Let  A  represent an ordered  k-partition  P = [P[1],...,P[k]]
# of  [1..n],  where  A  is a dense list of length  n  of 
# elements of  [1..k],  such that  A[i]=j  means that  i  is 
# in the  j-th  part  P[j]  of  P. 
#
# Let  R  be a subset of  [1..n]  with  A[r]=k  for all 
# r in R  (i.e.  R  is contained in  P[k]),  and let   newpoint
# be an element of  [1..n]  such that  A[newpoint] < k  (i.e 
# newpoint  is in one of  P[1],...,P[k-1]).
#
# Furthermore, suppose that  |P[1]|+...+|P[k-1]|<=(k-1)*n/k,  and 
# for every  k-subset  K  in  orb  not containing   newpoint,
# if the intersection of  K  with each of  P[1],...,P[k-1]
# has size 1, then the remaining point of  K  is in  R.
# 
# Then this function returns `true' if for every  k-partition  Q  of
# [1..n]  satisfying:
#   - Q[i]  contains  P[i]  for  i=1,...,k-1,
#   - no element of  R  is in  Q[k],
#   - |Q[k]| >= n/k,
# there is a  k-set  in  orb  forming a transversal of  Q.
#
# The method is to try to build a counterexample, and to return 
# `true' if (provably) no counterexample exists. 
# Otherwise, this function returns a counterexample, that is,
# a  k-partition  Q  of  [1..n], satisfying the properties above 
# with  R=[],  such that no k-set  in  orb  is a transversal of  Q.
#
# It is assumed that  done  is a set of  (k-1)-subsets of  [1..n]
# such that, for every  D  in  done:
#   - D  is least in its  G-orbit,
#   - for every  k-partition  Q  of  [1..n],  with  |Q[k]| >= n/k
#     and  D  forming a transversal of  [Q[1],...,Q[k-1]],
#     there is an element of  orb  forming a transversal of  Q.
#
local transversalproperty,n;

transversalproperty := function(A,asum,R,newpoint)
#
# Wrapped recursive function doing all the real work.
# 
# asum  is the number of elements of  A  that are  < k.
# It is assumed that  asum+Length(R) <= (k-1)*n/k. 
#
local v,K,r,tp,i,kpoint;
for v in Adjacency(orbgraph,newpoint) do
   K:=Concatenation(orbgraph.names[v],[newpoint]);
   if IsInjectiveListTrans(K,A) then
      # A[K[1]],...,A[K[k]]  are distinct, so  K  forms a transversal of  P.
      kpoint:=First(K,x->A[x]=k);
      AddSet(R,kpoint);
      # No element of  R  can be in the  k-th  part of a counterexample.
      if asum+Length(R) > (k-1)*n/k then
         # No counterexample exists.
         return true;
      elif done<>[] then
         if SmallestImageSet(G,Difference(K,[kpoint])) in done then
            return true;
         fi;
      fi;
   fi;
od;
if R=[] then
   #  A  defines a counterexample, so we return the ordered partition 
   # defined by  A.
   return GRAPE_NumbersToSets(A);
fi;
r:=Remove(R);
for i in [1..k-1] do
   # Try to build a counterexample with  r  in the  i-th part.
   A[r]:=i;
   tp:=transversalproperty(A,asum+1,ShallowCopy(R),r);
   A[r]:=k; # reset the value of A
   if tp<>true then
      # tp  is a counterexample.
      return tp;
   fi;
od;
return true;
end;

#
# begin TransversalProperty 
#
n:=LargestMovedPoint(G);
if k<2 or k>n then
   Error("must have 2 <= <k> <= LargestMovedPoint(<G>)");
fi;
return transversalproperty(A,Number(A,a->a<k),ShallowCopy(R),newpoint);
end;

tpmain:=function(G,rep,shortreps) 
#
# Let  G  be a permutation group on  [1..n],  where  n  is the
# largest point moved by  G,  and let  k:=Length(rep).
#
# This boolean function determines whether, for each
# k-partition of  [1..n],  there is a transversal in 
# the G-orbit of the k-set rep.
# 
# The parameter  shortreps  should be a list consisting of the lex-least
# representatives for the  G-orbits  of  (k-1)-subsets of  [1..n].
#
# It is assumed that  2<=k<=n. 
#
# This function makes use of the external C program tpexternal, 
# unless TRANSVERSALPROPERTIES_tpexternal_maxnum<=0 or 
# G  is not transitive on  [1..n].
#
local n,k,in_file,in_stream,out_file,out_stream,status,result,done,i,A,
   tp,tpexternal_num,orbgraph;
n:=LargestMovedPoint(G);
k:=Length(rep);
if k<2 or k>n then
   Error("must have 2 <= <k> <= LargestMovedPoint(<G>)");
fi;
if not IsTransitive(G,[1..n]) then
   tpexternal_num:=0;
else
   tpexternal_num:=
      Minimum(TRANSVERSALPROPERTIES_tpexternal_maxnum,Length(shortreps));
fi;
orbgraph:=OrbGraph(G,rep);
if tpexternal_num>0 then
   # We make use of the external C program.
   in_file:=Filename(TRANSVERSALPROPERTIES_tmpdir,"in_file");
   out_file:=Filename(TRANSVERSALPROPERTIES_tmpdir,"out_file");
   RemoveFile(in_file);  # in case there is a leftover copy
   RemoveFile(out_file); # in case there is a leftover copy
   in_stream:=OutputTextFile(in_file,false);
   if in_stream=fail then
       Error("tpmain: error opening output text stream using file ",in_file); 
   fi;
   SetPrintFormattingStatus(in_stream,false);
   PrintStreamTpexternalInput(in_stream,G,k,orbgraph,
      shortreps{[1..tpexternal_num]});
   CloseStream(in_stream);
   in_stream:=InputTextFile(in_file);
   if in_stream=fail then
      Error("tpmain: error opening input text stream using file ",in_file);
   fi;
   out_stream:=OutputTextFile(out_file,false);
   if out_stream=fail then
       Error("tpmain: error opening output text stream using file ",out_file);
   fi;
   SetPrintFormattingStatus(out_stream,false);
   Info(TRANSVERSALPROPERTIES_info,3,
      "Runtimes in milliseconds before calling tpexternal: ",Runtimes());
   status:=GRAPE_Exec(TRANSVERSALPROPERTIES_tpexternal_exe, 
      [],in_stream,out_stream);
   Info(TRANSVERSALPROPERTIES_info,3,
      "Runtimes in milliseconds after calling tpexternal: ",Runtimes());
   if status<>0 then
     Error("tpmain: exit code ",status," returned by tpexternal;\n",
      "returned results may be wrong");
   fi;
   CloseStream(out_stream);
   out_stream:=InputTextFile(out_file);
   result:=ReadLine(out_stream);
   CloseStream(in_stream); 
   CloseStream(out_stream); 
   RemoveFile(in_file);
   RemoveFile(out_file);
   if result=fail then
      Error("tpmain: result unavailable");
   fi;
   result:=Int(Chomp(result));
   if result=0 then
      return false;
   fi;
   if result<>1 then 
      Error("tpmain: invalid result");
   fi;
   # At this point, the result is 1 (==true).
   if Length(shortreps)=tpexternal_num then
      return true;
   fi;
fi;
# Here, we are finished with the external C program, 
# but more work is required.
done:=Set(shortreps{[1..tpexternal_num]});
for i in [tpexternal_num+1..Length(shortreps)] do 
   A:=ListWithIdenticalEntries(n,k);
   A{shortreps[i]}:=[1..k-1];
   Info(TRANSVERSALPROPERTIES_info,3,
      "Runtimes in milliseconds before calling TransversalProperty: ",
      Runtimes());
   tp:=TransversalProperty(G,k,orbgraph,A,[],shortreps[i][1],done);
   Info(TRANSVERSALPROPERTIES_info,3,
      "Runtimes in milliseconds after calling TransversalProperty: ",
      Runtimes());
   if tp<>true then
      Info(TRANSVERSALPROPERTIES_info,2,
         "tpmain returns false for rep=",rep,"  shortrep=",shortreps[i],
         "  first k-1 parts = ",tp{[1..k-1]});
      return false;
   else
      AddSet(done,shortreps[i]);
   fi;
od;
return true;
end;

UniversalTransversalProperty := function(G,k,optional...)
#
# Suppose  G  is a permutation group on the domain
# [1..n],  where  n  is the largest point moved by  G,  and
# suppose  k  is an integer, with  2 <= k <= n.
#
# Then this function returns `true' if  G  has the property k-ut, 
# that is, for every  k-partition  P  of  [1..n]  and every 
# k-subset  K  of  [1..n],  there is a set in the  G-orbit  of  K
# which is a transversal of  P.
#
# Otherwise, this function returns `false'.
#
# The optional parameter optional[1] (default: G) must be a 
# permutation group on  [1..n],  containing  G  and normalizing  G.
# The use of this parameter may save some redundant checks of 
# G-orbits  of  k-subsets.
# 
local n,reps,rep,shortreps,shortrep,subreps,orbgraph,tp,C,A,stabsizes;
if not (IsPermGroup(G) and IsInt(k)) then
   Error("usage: UniversalTransversalProperty( <PermGrp>, <Int> [, <PermGrp> ] )");
fi;
n:=LargestMovedPoint(G);
if k<2 or k>n then
   Error("must have 2 <= <k> <= LargestMovedPoint(<G>)");
fi;
if Length(optional)>0 then
   C:=optional[1];
   if not (IsPermGroup(C) and LargestMovedPoint(C)=n and IsSubgroup(C,G) and IsNormal(C,G)) then
      Error("<C> must be a permutation group on the same domain as <G>, containing and normalizing <G>");
   fi;
else
   C:=G;
fi;
shortreps:=LeastSetRepresentatives(G,k-1);
if Length(shortreps)>k then
   # There are *no* witnessing k-sets, so the k-ut property does not hold.
   Info(TRANSVERSALPROPERTIES_info,1,
      "UniversalTransversalProperty: Length(shortreps)=",
      Length(shortreps),">k");
   return false;
fi;
reps:=LeastSetRepresentatives(C,k);
Info(TRANSVERSALPROPERTIES_info,1,
      "UniversalTransversalProperty: Length(shortreps)=",
      Length(shortreps)," Length(reps)=",Length(reps));
if Length(reps)=1 then
   if G=C or Length(LeastSetRepresentatives(G,k))=1 then
      # G is k-homogeneous, so the k-ut property holds
      Info(TRANSVERSALPROPERTIES_info,1,
         "UniversalTransversalProperty: G is k-homogeneous");
      return true;
   fi;
fi;
for rep in reps do
   subreps:=Set(Combinations(rep,k-1),x->SmallestImageSet(G,x));
   if not ForAll(shortreps,x->x in subreps) then
      Info(TRANSVERSALPROPERTIES_info,1,
         "UniversalTransversalProperty: rep=",rep,
         " does not contain representatives of all shortrep orbits");
      # rep is not a witnessing k-set, so the k-ut property does not hold
      return false;
   fi;
od;
stabsizes:=List(reps,x->Size(Stabilizer(G,x,OnSets)));
SortParallel(stabsizes,reps,function(x,y) return x>y; end);
Info(TRANSVERSALPROPERTIES_info,2,
      "UniversalTransversalProperty: stabsizes of reps=",
       Collected(stabsizes));
stabsizes:=List(shortreps,x->Size(Stabilizer(G,x,OnSets)));
SortParallel(stabsizes,shortreps);
Info(TRANSVERSALPROPERTIES_info,2,
      "UniversalTransversalProperty: stabsizes of shortreps=",
       Collected(stabsizes));
for rep in reps do
   Info(TRANSVERSALPROPERTIES_info,2,
      "UniversalTransversalProperty: testing orbit of: ",rep);
   tp:=tpmain(G,rep,shortreps);
   if tp<>true then
      # G does not have the k-ut property, as orbit of rep does
      # not contain a transversal for some k-partition.
      Info(TRANSVERSALPROPERTIES_info,1,
         "UniversalTransversalProperty: k-ut does not hold. ",
         "Orbit of ",rep," fails.");
      return false;
   fi; 
od;
return true;
end;

ExistentialTransversalProperty := function(G,k,optional...)
#
# Suppose  G  is a permutation group on the domain
# [1..n],  where  n  is the largest point moved by  G,  and
# suppose  k  is an integer, with  2 <= k <= n.
#
# If  G  has the  k-et  property (i.e. for some  k-subset  
# K  of  [1..n]:  for every k-partition  P  of  [1..n], 
# there is a set in the  G-orbit  of  K  that is a transversal of  P),
# then this function returns  `true'.
#
# If  G  does not have the  k-et  property, then this function
# returns  `false'.
#
# The optional parameter  optional[1]  (default: G)  must be a 
# permutation group on  [1..n],  containing  G  and normalizing  G.
# The use of this parameter may save some redundant checks of 
# G-orbits  of  k-subsets.
# 
local n,reps,rep,shortreps,shortrep,subreps,orbgraph,tp,C,A,stabsizes;
if not (IsPermGroup(G) and IsInt(k)) then
   Error("usage: ExistentialTransversalProperty( <PermGrp>, <Int> [, <PermGrp> ] )");
fi;
n:=LargestMovedPoint(G);
if k<2 or k>n then
   Error("must have 2 <= <k> <= LargestMovedPoint(<G>)");
fi;
if Length(optional)>0 then
   C:=optional[1];
   if not (IsPermGroup(C) and LargestMovedPoint(C)=n and IsSubgroup(C,G) and IsNormal(C,G)) then
      Error("<C> must be a permutation group on the same domain as <G>, containing and normalizing <G>");
   fi;
else
   C:=G;
fi;
shortreps:=LeastSetRepresentatives(G,k-1);
if Length(shortreps)>k then
   # There are *no* witnessing k-sets, so the k-et property cannot hold.
   Info(TRANSVERSALPROPERTIES_info,1,
      "ExistentialTransversalProperty: Length(shortreps)=",
      Length(shortreps),">k");
   return false;
fi;
reps:=LeastSetRepresentatives(C,k);
Info(TRANSVERSALPROPERTIES_info,1,
      "ExistentialTransversalProperty: Length(shortreps)=",
      Length(shortreps)," Length(reps)=",Length(reps));
if Length(reps)=1 then
   if G=C or Length(LeastSetRepresentatives(G,k))=1 then
      # G is k-homogeneous, so the k-et property holds
      Info(TRANSVERSALPROPERTIES_info,1,
         "ExistentialTransversalProperty: G is k-homogeneous");
      return true;
   fi;
fi;
stabsizes:=List(reps,x->Size(Stabilizer(G,x,OnSets)));
SortParallel(stabsizes,reps);
Info(TRANSVERSALPROPERTIES_info,2,
      "ExistentialTransversalProperty: stabsizes of reps=",
       Collected(stabsizes));
stabsizes:=List(shortreps,x->Size(Stabilizer(G,x,OnSets)));
SortParallel(stabsizes,shortreps);
Info(TRANSVERSALPROPERTIES_info,2,
      "ExistentialTransversalProperty: stabsizes of shortreps=",
       Collected(stabsizes));
for rep in reps do
   subreps:=Set(Combinations(rep,k-1),x->SmallestImageSet(G,x));
   if not ForAll(shortreps,x->x in subreps) then
      Info(TRANSVERSALPROPERTIES_info,1,
         "ExistentialTransversalProperty: rep=",rep,
         " does not contain representatives of all shortrep orbits");
      # rep is not a witnessing k-set
      continue;
   fi;
   Info(TRANSVERSALPROPERTIES_info,2,
      "ExistentialTransversalProperty: testing orbit of: ",rep);
   tp:=tpmain(G,rep,shortreps);
   if tp=true then
      # G has the k-et property, witnessed by rep. 
      Info(TRANSVERSALPROPERTIES_info,1,
         "ExistentialTransversalProperty: k-et holds with witness: ",rep);
      return true;
   fi; 
od;
return false;
end;

StrongTransversalProperty := function(G,k,orb,A)
#
# Let  G  be a permutation group on  [1..n],  where  n  is the
# largest point moved by  G,  and let  orb  be a  G-orbit  of a tuple  
# [T,U],  where  T  is a 2-subset of  [1..n]  and  U  is a  (k-1)-subset  
# of  [1..n]  disjoint from  T.  It is assumed that  2 <= k <= n-1. 
#
# Let  A  represent an ordered  k-partition  P = [P[1],...,P[k]]
# of  [1..n],  where  A  is a dense list of length  n  of 
# elements of  [1..k],  such that  A[i]=j  means that  i  is 
# in the  j-th  part  P[j]  of  P. 
#
# Furthermore, suppose that  |P[1]|+...+|P[k-1]|<=(k-1)*n/k.
# 
# Then this function returns `true' if for every  k-partition  Q  of
# [1..n]  satisfying:
#
#   - Q[i]  contains  P[i]  for  i=1,...,k-1,
#   - |Q[k]| >= n/k,
#
# there is an element  g in G  such that: 
#
#    - T[1]^g  and  T[2]^g  are in the same part of  Q, 
#    - Union([T[1]],U)^g  is a transversal of  Q.
#
# The method is to try to build a counterexample, and to return 
# `true' if (provably) no counterexample exists. 
# Otherwise, this function returns a counterexample, that is,
# a  k-partition  Q  of  [1..n],  satisfying: 
#
#   - Q[i]  contains  P[i]  for  i=1,...,k-1,
#   - |Q[k]| >= n/k,
#
# such that there is *no* element  g in G  such that: 
#
#    - T[1]^g  and  T[2]^g  are in the same part of  Q, 
#    - Union([T[1]],U)^g  is a transversal of  Q.
#
local strongtransversalproperty,n;

strongtransversalproperty := function(A,asum)
#
# Wrapped recursive function doing all the real work.
# 
# The variables  k,  n,  and  orb  are global.
#
# asum  is the number of elements of  A  that are  < k.
#
local elm,a,b,K,r,s,tp,i,kpoint,R,S,gamma;
R:=[];
# R  is maintained as a subset of  [1..n],  such that no element
# of  R  can be in the  k-th  part of a counterexample. 
S:=[];
# S  is maintained as a set of 2-subsets of  [1..n],  such that,
# if  [a,b] in S,  then either  a  or  b  (or both) cannot be in
# the  k-th  part of a counterexample.
for elm in orb do
   # loop invariant: 
   #   -  R  is a subset of  P[k],
   #   -  S  is a set of  2-subsets  of  P[k],  such that
   #      every element of  S  is disjoint from  R.
   a:=elm[1][1];
   b:=elm[1][2]; 
   if A[a]=A[b] then
      K:=Concatenation(elm[2],[a]);
      if IsInjectiveListTrans(K,A) then
         # A[K[1]],...,A[K[k]] are distinct, so  K  forms a transversal of  P.
         kpoint:=First(K,x->A[x]=k);
         if kpoint=a then
            # Either  a  or  b  (or both) cannot be in the  k-th  part
            # of a counterexample.
            if not ([a,b] in S) and not (a in R) and not (b in R) then
               AddSet(S,[a,b]);
               if asum+Length(R)+1 > (k-1)*n/k then
                  # No counterexample exists.
                  return true;
               fi;
            fi;
         elif not (kpoint in R) then
            # kpoint  cannot be in the  k-th  part of a counterexample.
            AddSet(R,kpoint);
            S:=Filtered(S,x->not (kpoint in x));
            if asum+Length(R) > (k-1)*n/k then
               return true;
            elif Length(S)>0 and asum+Length(R)+1 > (k-1)*n/k then
               return true;
            fi;
         fi;
      fi;
   fi;
od;
if R=[] and S=[] then
   # A  represents a counterexample, so we return this (ordered) partition.
   return GRAPE_NumbersToSets(A);
fi;
if Length(S)>1 and asum+Length(R)+Length(S)>(k-1)*n/k then
   gamma:=Graph(Group(()),S,{x,g}->x,{x,y}->Length(Intersection(x,y))=1,true);
   if asum+Length(R)+Length(IndependentSet(gamma)) > (k-1)*n/k then
      # There are not enough elements left from  [1..n]  to form the 
      # k-th  part of a counterexample. 
      return true;
   fi;
fi;
if R<>[] then
   r:=Remove(R);
   for i in [1..k-1] do
      # Try to build a counterexample with  r  in the  i-th  part.
      A[r]:=i;
      tp:=strongtransversalproperty(A,asum+1);
      A[r]:=k;  # reset the value of A
      if tp<>true then
         #  tp  is a counterexample.
         return tp;
      fi;
   od;
   return true;
fi;
# Here, we must have  R=[]  and  S<>[]. 
s:=Remove(S);
for r in s do
   for i in [1..k-1] do
      A[r]:=i;
      # Try to build a counterexample with  r  in the  i-th  part.
      tp:=strongtransversalproperty(A,asum+1);
      A[r]:=k;  # reset the value of A
      if tp<>true then
         #  tp  is a counterexample.
         return tp;
      fi;
   od;
od;
return true;
end;

#
# begin StrongTransversalProperty 
#
n:=LargestMovedPoint(G);
if k<2 or k>n-1 then
   Error("must have 2 <= <k> <= LargestMovedPoint(<G>)-1");
fi;
return strongtransversalproperty(A,Number(A,a->a<k));
end;

strongtpmain:=function(G,rep,shortreps) 
#
# Let  G  be a permutation group on  [1..n],  where  n  is the
# largest point moved by  G,  and let  rep  be a tuple  [T,U],  where
# T  is a 2-subset of  [1..n]  and  U  is a  (k-1)-subset  of  [1..n]
# disjoint from  T.  It is assumed that  2 <= k <= n-1. 
# The parameter  shortreps  should be a list consisting of the lex-least
# representatives for the  G-orbits  of  (k-1)-subsets of  [1..n].
#
# Then this boolean function returns `true' iff  rep  is a witness
# for the "strong k-et" property of  G, that is, for every  k-partition
# P  of  [1..n],  there is a  g  in  G  such that:
#
#    - T[1]^g  and  T[2]^g  are in the same part of  P 
#    - Union([T[1]],U)^g  is a transversal of  P.
#  
local n,k,orb,result,i,A,tp;
n:=LargestMovedPoint(G);
k:=Length(rep[2])+1;
if k<2 or k>n-1 then
   Error("must have 2 <= <k> <= LargestMovedPoint(<G>)-1");
fi;
orb:=Set(Orbit(G,rep,OnTuplesSets)); 
for i in [1..Length(shortreps)] do 
   A:=ListWithIdenticalEntries(n,k);
   A{shortreps[i]}:=[1..k-1];
   Info(TRANSVERSALPROPERTIES_info,3,
      "Runtimes in milliseconds before calling StrongTransversalProperty: ",
      Runtimes());
   tp:=StrongTransversalProperty(G,k,orb,A);
   Info(TRANSVERSALPROPERTIES_info,3,
      "Runtimes in milliseconds after calling StrongTransversalProperty: ",
      Runtimes());
   if tp<>true then
      Info(TRANSVERSALPROPERTIES_info,2,
         "strongtpmain returns false for rep=",rep,"  shortrep=",shortreps[i],
         "  first k-1 parts = ",tp{[1..k-1]});
      return false;
   fi;
od;
return true;
end;

StrongUniversalTransversalProperty := function(G,k,optional...)
#
# Suppose  G  is a permutation group on the domain
# [1..n],  where  n  is the largest point moved by  G,  and
# suppose  k  is an integer, with  2 <= k <= n-1.
#
# Then this function returns `true' if  G  has the property 
# strong k-ut.  Otherwise, this function returns `false'.
#
# The optional parameter optional[1] (default: G) must be a 
# permutation group on  [1..n],  containing  G  and normalizing  G.
# The use of this parameter may save some redundant checks of G-orbits.
# 
local n,H,reps,found,LL,L,M,rep,shortreps,shortrep,C,tp,A,stabsizes,testmode;
if not (IsPermGroup(G) and IsInt(k)) then
   Error("usage: StrongUniversalTransversalProperty( <PermGrp>, <Int> [, <PermGrp> ] )");
fi;
n:=LargestMovedPoint(G);
if k<2 or k>n-1 then
   Error("must have 2 <= <k> <= LargestMovedPoint(<G>)-1");
fi;
if Length(optional)>0 then
   C:=optional[1];
   if not (IsPermGroup(C) and LargestMovedPoint(C)=n and IsSubgroup(C,G) and IsNormal(C,G)) then
      Error("<C> must be a permutation group on the same domain as <G>, containing and normalizing <G>");
   fi;
else
   C:=G;
fi;
testmode:=TRANSVERSALPROPERTIES_testmode;
if (not testmode) and Transitivity(G,[1..n])>k then
   Info(TRANSVERSALPROPERTIES_info,1,
         "StrongUniversalTransversalProperty: Transitivity(G,[1..n])>k");
   return true;
fi;
shortreps:=LeastSetRepresentatives(G,k-1);
if (not testmode) and Length(shortreps)>1 then
   Info(TRANSVERSALPROPERTIES_info,1,
      "StrongUniversalTransversalProperty: G is not (k-1)-homogeneous");
   return false;
fi;
LL:=LeastSetRepresentatives(C,k+1);
if not testmode then
   if Length(LeastSetRepresentatives(G,k))>1 then
      # G is not k-homogeneous
      if not UniversalTransversalProperty(G,k,C) then
         Info(TRANSVERSALPROPERTIES_info,1,
            "StrongUniversalTransversalProperty: G does not satisfy k-ut");
         return false;
      fi;
   else
      found:=false;
      for L in LL do
         H:=Action(Stabilizer(G,L,OnSets),L);
         if LargestMovedPoint(H)<Length(L)
            or Length(LeastSetRepresentatives(H,2))>1 then
            found:=true;
            break;
         fi;
      od;
      if not found then
         Info(TRANSVERSALPROPERTIES_info,1,
            "StrongUniversalTransversalProperty: ",
            "for every (k+1)-subset of [1..n], the action of its ",
            "G-stabilizer on it is 2-homogeneous");
         return true;
      fi;
   fi;
fi;
reps:=[];
for L in LL do
   H:=Stabilizer(C,L,OnSets);
   for M in Set(Orbits(H,Combinations(L,2),OnSets),Set) do
      Add(reps,[M[1],Difference(L,M[1])]);
   od;
od;
Info(TRANSVERSALPROPERTIES_info,1,
      "StrongUniversalTransversalProperty: Length(reps)=",Length(reps));
stabsizes:=List(reps,x->Size(Stabilizer(G,x,OnTuplesSets)));
SortParallel(stabsizes,reps,function(x,y) return x>y; end);
Info(TRANSVERSALPROPERTIES_info,2,
      "StrongUniversalTransversalProperty: stabsizes of reps=",
       Collected(stabsizes));
for rep in reps do
   Info(TRANSVERSALPROPERTIES_info,2,
      "StrongUniversalTransversalProperty: testing orbit of: ",rep);
   tp:=strongtpmain(G,rep,shortreps);
   if tp<>true then
      # G does not have the strong k-ut property
      Info(TRANSVERSALPROPERTIES_info,1,
         "StrongUniversalTransversalProperty: strong k-ut does not hold. ",
         "Orbit of ",rep," fails.");
      return false;
   fi; 
od;
return true;
end;

OrbitHoughtonGraph := function(G,P,A)
#
# returns the orbit Houghton graph w.r.t. the permutation 
# group  G  on [1..n], the k-partition  P  of  [1..n], and the 
# (non-empty) k-subset  A  of [1..n].
#
# The degree  n  of  G  is taken to be its largest moved point,
# unless  G  is trivial, in which case  n  is taken to be 1. 
# If  P  is given as an ordered partition, then  P  is taken to be  Set(P).
#
local act,rel,n,partitionorb,setorb;

act:=function(x,g)
if IsInt(x[1]) then
   # x is a (non-empty) set of points
   return OnSets(x,g);
else
   # x is a partition
   return OnSetsDisjointSets(x,g);
fi;
end;

rel:=function(x,y)
#
# This boolean function returns `true' iff  x  is a k-subset 
# and  y  is a k-partition with  x  a transversal of  y,  
# or  y  is a k-subset and  x  is a  k-partition with  y  
# a transversal of  x.
# 
if IsInt(x[1]) and (not IsInt(y[1])) then
   return ForAll(y,part->Size(Intersection(x,part))=1);
elif IsInt(y[1]) and (not IsInt(x[1])) then
   return ForAll(x,part->Size(Intersection(y,part))=1);
else
   return false;
fi;
end;

if not (IsPermGroup(G) and IsList(P) and IsSet(A)) then
   Error("usage: OrbitHoughtonGraph( <PermGroup>, <List>, <Set> )");
fi;
n:=LargestMovedPoint(G);
if n=0 then
  n:=1;
fi;
if not (A<>[] and Length(A)=Length(P) and IsSubset([1..n],A) 
         and Union(P)=[1..n] and ForAll(P,x->IsSet(x) and x<>[]) 
         and Sum(List(P,Length))=n) then
   Error("P must be a k-partition and A must be a nonempty k-subset of [1..n]");
fi;
P:=Set(P);
partitionorb:=Set(Orbit(G,P,OnSetsDisjointSets));
setorb:=Set(Orbit(G,A,OnSets));
return Graph(G,Concatenation(partitionorb,setorb),act,rel,true);
end;

OrderedLiftOfHoughtonGraph := function(G,P,A)
#
# returns the "tuplized" orbit Houghton graph w.r.t. the permutation 
# group  G  on [1..n],  the k-partition  P  of  [1..n],  and the 
# (non-empty) k-subset  A  of [1..n].
#
# The degree  n  of  G  is taken to be its largest moved point,
# unless  G  is trivial, in which case  n  is taken to be 1. 
# If  P  is given as an ordered partition, then  P  is taken to be  Set(P).
#
local act,rel,n,partitionorb,setorb,tuplizedpartitionorb,tuplizedsetorb;

act:=function(x,g)
if IsInt(x[1]) then
   # x is a (non-empty) k-tuple of points
   return OnTuples(x,g);
else
   # x is an ordered k-partition
   return OnTuplesSets(x,g);
fi;
end;

rel:=function(x,y)
#
# This boolean function returns `true' iff  x  is a k-tuple (of points)
# and  y  is an ordered  k-partition with  x[i] in y[i]  for i=1,...,k,
# or  y  is a k-tuple (of points) and  x  is an ordered k-partition with
# y[i] in x[i]  for i=1,...,k.
# 
if IsInt(x[1]) and (not IsInt(y[1])) then
   return ForAll([1..Length(x)],i->x[i] in y[i]);
elif IsInt(y[1]) and (not IsInt(x[1])) then
   return ForAll([1..Length(y)],i->y[i] in x[i]);
else
   return false;
fi;
end;

if not (IsPermGroup(G) and IsList(P) and IsSet(A)) then
   Error("usage: OrderedLiftOfHoughtonGraph( <PermGroup>, <List>, <Set> )");
fi;
n:=LargestMovedPoint(G);
if n=0 then
  n:=1;
fi;
if not (A<>[] and Length(A)=Length(P) and IsSubset([1..n],A) 
         and Union(P)=[1..n] and ForAll(P,x->IsSet(x) and x<>[]) 
         and Sum(List(P,Length))=n) then
   Error("P must be a k-partition and A must be a nonempty k-subset of [1..n]");
fi;
P:=Set(P);
partitionorb:=Set(Orbit(G,P,OnSetsDisjointSets));
tuplizedpartitionorb:=Union(List(partitionorb,PermutationsList));
setorb:=Set(Orbit(G,A,OnSets));
tuplizedsetorb:=Union(List(setorb,PermutationsList));
return Graph(G,Concatenation(tuplizedpartitionorb,tuplizedsetorb),act,rel,true);
end;

TuplizedOrbitHoughtonGraph := OrderedLiftOfHoughtonGraph;

IdempotentGenerationProperty := function(G,k)
#
# Suppose  G  is a permutation group on  [1..n],
# where  n:=LargestMovedPoint(G),  and  k  is an 
# integer with  1 < k < n.
# 
# Then this function returns `true' if  G  satisfies
# the  k-id  property, and `false' if not.
#
local n,setreps,partitionreps,set,partition;
if not (IsPermGroup(G) and IsInt(k)) then
   Error("usage: IdempotentGenerationProperty( <PermGrp>, <Int> )");
fi;
n:=LargestMovedPoint(G);
if k<=1 or k>=n then
   Error("must have  1 < k < LargestMovedPoint(G)");
fi;
if NrMovedPoints(G)=n and (IsNaturalSymmetricGroup(G) or IsNaturalAlternatingGroup(G)) then
   # G has the k-id property
   Info(TRANSVERSALPROPERTIES_info,1,
      "IdempotentGenerationProperty: k-id holds since G is S_n or A_n");
   return true;
fi; 
if not UniversalTransversalProperty(G,k) then
   # G does not have the k-ut property and so does not have k-id
   Info(TRANSVERSALPROPERTIES_info,1,
      "IdempotentGenerationProperty: k-ut does not hold ",
      "so k-id does not hold.");
   return false;
fi; 
partitionreps:=Set(
   OrbitsDomain(G,PartitionsSet([1..n],k),OnSetsDisjointSets),Minimum );
setreps:=LeastSetRepresentatives(G,k);
Info(TRANSVERSALPROPERTIES_info,2,
   "IdempotentGenerationProperty: no. of k-partition orbits = ",
   Length(partitionreps),", no. of k-set orbits = ",Length(setreps));
for partition in partitionreps do
   for set in setreps do
      if not IsConnectedGraph(OrbitHoughtonGraph(G,partition,set)) then
         # G does not have the k-id property
         Info(TRANSVERSALPROPERTIES_info,1,
            "IdempotentGenerationProperty: k-id does not hold. ",
            "Orbit Houghton graph not connected for: ",
            partition,", ",set);
         return false;
      fi; 
   od;
od;
Info(TRANSVERSALPROPERTIES_info,2,
   "IdempotentGenerationProperty: k-RCP holds for all orbit-pairs");
for partition in partitionreps do
   for set in setreps do
      if not IsConnectedGraph(OrderedLiftOfHoughtonGraph(G,partition,set)) then
         # G does not have the k-id property
         Info(TRANSVERSALPROPERTIES_info,1,
            "IdempotentGenerationProperty: k-id does not hold. ",
            "ordered lift of Houghton graph not connected for: ",
            partition,", ",set);
         return false;
      fi; 
   od;
od;
return true;
end;

