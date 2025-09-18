#
# Functions to determine transversal properties of finite
# permutation groups.
#
# Leonard Soicher, 18 September 2025.
#
DeclareInfoClass("info_tp");
SetInfoLevel(info_tp,2);

LoadPackage("grape");

LeastSetRepresentatives := function(G,k)
#
# Suppose  G  is a permutation group on  [1..n],
# where  n:=LargestMovedPoint(G),  and  k  is a 
# non-negative integer. 
# 
# Then this function returns the set of lex-least 
# representatives for the orbits of  G  on the  k-subsets
# of  [1..n].
#
if not (IsPermGroup(G) and IsInt(k)) then
   Error("usage: LeastSetRepresentatives( <PermGrp>, <Int> )");
fi;
if k<0 then
   Error("must have  <k> >= 0"); 
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

TransversalProperty := function(n,k,orbgraph,A,R,newpoint)
#
# Let  orb  be a  G-orbit  of  k-subsets  of  [1..n], 
# with  k>1,  as represented by  orbgraph.
# Let  A  represent an ordered  k-partition  [P[1],...,P[k]]
# of  [1..n],  where  A  is a dense list of length  n  of 
# elements of  [1..k],  such that  A[i]=j  means that  i  is 
# in the  j-th  part  P[j]  of  P. 
# Let  R  be a subset of  [1..n]  with  A[r]=k  for all 
# r in R  (i.e.  R  is contained in  P[k]),  and let   newpoint
# be an element of  [1..n]   such that  A[newpoint] < k  (i.e 
# newpoint  is in one of  P[1],...,P[k-1]).
#
# Furthermore, suppose that  |P[1]|+...+|P[k-1]|<=(k-1)*n/k,  and 
# for every  k-subset  K  in   orb  not containing   newpoint,
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
local v,K,r,tp,i,asum;
Info(info_tp,3,"TransversalProperties: P=",GRAPE_NumbersToSets(A),
   "  R=",R);
asum:=Number(A,x->x<k);
for v in Adjacency(orbgraph,newpoint) do
   K:=Concatenation(orbgraph.names[v],[newpoint]);
   if IsInjectiveListTrans(K,A) then
      # A[K[1]],...,A[K[k]] are distinct
      AddSet(R,First(K,x->A[x]=k));
      if asum+Length(R) > (k-1)*n/k then
         return true;
      fi;
   fi;
od;
if R=[] then
   return GRAPE_NumbersToSets(A);
fi;
r:=Remove(R);
for i in [1..k-1] do
   A[r]:=i;
   tp:=TransversalProperty(n,k,orbgraph,A,ShallowCopy(R),r);
   if tp<>true then
      return tp;
   fi;
   A[r]:=k;
od;
return true;
end;

UniversalTransversalProperty := function(G,k,optional...)
#
# Suppose  G  is a permutation group on the domain
# [1..n],  where  n  is the largest point moved by  G, and
# suppose k is an integer, with 1 < k <= n/2.
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
local n,reps,rep,shortreps,shortrep,subreps,orbgraph,tp,C,A;
if not (IsPermGroup(G) and IsInt(k)) then
   Error("usage: UniversalTransversalProperty( <PermGrp>, <Int> [, <PermGrp> ] )");
fi;
n:=LargestMovedPoint(G);
if not (k>1 and k<=n/2) then
   Error("must have  1 < <k> <= LargestMovedPoint(<G>)/2"); 
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
   Info(info_tp,1,"UniversalTransversalProperty: Length(shortreps)=",
      Length(shortreps),">k");
   return false;
fi;
reps:=LeastSetRepresentatives(C,k);
if Length(reps)=1 then
   if G=C or Length(LeastSetRepresentatives(G,k))=1 then
      # G is k-homogeneous, so the k-ut property holds
      Info(info_tp,1,"UniversalTransversalProperty: G is k-homogeneous");
      return true;
   fi;
fi;
for rep in reps do
   subreps:=Set(Combinations(rep,k-1),x->SmallestImageSet(G,x));
   if not ForAll(shortreps,x->x in subreps) then
      Info(info_tp,1,"UniversalTransversalProperty: rep=",rep,
         " does not contain representatives of all shortrep orbits");
      # rep is not a witnessing k-set, so the k-ut property does not hold
      return false;
   fi;
od;
for rep in reps do
   orbgraph:=OrbGraph(G,rep);
   for shortrep in shortreps do 
      A:=ListWithIdenticalEntries(n,k);
      A{shortrep}:=[1..k-1];
      tp:=TransversalProperty(n,k,orbgraph,A,[],shortrep[1]);
      Info(info_tp,2,"UniversalTransversalProperty: rep=",rep,
         " shortrep=",shortrep," tp=",tp);
      if tp<>true then
         #  G  does not have the k-ut property.
         return false;
      fi;
   od;
od;
return true;
end;

ExistentialTransversalProperty := function(G,k,optional...)
#
# Suppose  G  is a permutation group on the domain
# [1..n],  where  n  is the largest point moved by  G,  and
# suppose  k  is an integer, with  1 < k <= n/2.
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
local n,reps,rep,shortreps,shortrep,subreps,orbgraph,tp,C,A;
if not (IsPermGroup(G) and IsInt(k)) then
   Error("usage: ExistentialTransversalProperty( <PermGrp>, <Int> [, <PermGrp> ] )");
fi;
n:=LargestMovedPoint(G);
if not (k>1 and k<=n/2) then
   Error("must have  1 < <k> <= LargestMovedPoint(<G>)/2"); 
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
   Info(info_tp,1,"ExistentialTransversalProperty: Length(shortreps)=",
      Length(shortreps),">k");
   return false;
fi;
reps:=LeastSetRepresentatives(C,k);
if Length(reps)=1 then
   if G=C or Length(LeastSetRepresentatives(G,k))=1 then
      # G is k-homogeneous, so the k-et property holds
      Info(info_tp,1,"ExistentialTransversalProperty: G is k-homogeneous");
      return true;
   fi;
fi;
for rep in reps do
   subreps:=Set(Combinations(rep,k-1),x->SmallestImageSet(G,x));
   if not ForAll(shortreps,x->x in subreps) then
      Info(info_tp,1,"ExistentialTransversalProperty: rep=",rep,
         " does not contain representatives of all shortrep orbits");
      # rep is not a witnessing k-set
      continue;
   fi;
   orbgraph:=OrbGraph(G,rep);
   for shortrep in shortreps do 
      A:=ListWithIdenticalEntries(n,k);
      A{shortrep}:=[1..k-1];
      tp:=TransversalProperty(n,k,orbgraph,A,[],shortrep[1]);
      Info(info_tp,2,"ExistentialTransversalProperty: rep=",rep,
         " shortrep=",shortrep," tp=",tp);
      if tp<>true then
         break;
      fi;
   od;
   if tp=true then
      return true;
   fi;
od;
return false;
end;
