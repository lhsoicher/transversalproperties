#
# Functions to determine transversal properties of (finite degree)
# permutation groups.
#
# Leonard Soicher, 21 February 2026.
#
TRANSVERSALPROPERTIES_tpexternal_maxnum:=1;
# for each rep, the maximum number of shortreps to be handled by the 
# external program tpexternal

TRANSVERSALPROPERTIES_tpexternal_exe:="/home/lsoicher/bin/tpexternal";
# the external program's executable file

TRANSVERSALPROPERTIES_tmpdir:=DirectoryTemporary();
# for files to communicate with tpexternal

DeclareInfoClass("TRANSVERSALPROPERTIES_info");
SetInfoLevel(TRANSVERSALPROPERTIES_info,2);

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
# Otherwise, this function returns a  k-partition  Q  of  [1..n], 
# satisfying the properties above with  R=[],  such that no
# k-set  in  orb  is a transversal of  Q.
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
      # A[K[1]],...,A[K[k]] are distinct
      kpoint:=First(K,x->A[x]=k);
      AddSet(R,kpoint);
      if asum+Length(R) > (k-1)*n/k then
         return true;
      elif done<>[] then
         if SmallestImageSet(G,Difference(K,[kpoint])) in done then
            return true;
         fi;
      fi;
   fi;
od;
if R=[] then
   #  A  defines a k-partition such that no element of  orb  is
   # a transversal. 
   return GRAPE_NumbersToSets(A);
fi;
r:=Remove(R);
for i in [1..k-1] do
   A[r]:=i;
   tp:=transversalproperty(A,asum+1,ShallowCopy(R),r);
   if tp<>true then
      return tp;
   fi;
   A[r]:=k;
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
return transversalproperty(A,Number(A,a->a<k),R,newpoint);
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
# The parameter  shortreps  should be a list of lex-least
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
# More work is required.
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
# suppose k is an integer, with  2 <= k <= n.
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
