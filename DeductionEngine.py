import numpy as np


sup = [">", "<", "="] #relations
inf = ["+","-",".","/", "^"] #functions
#all variables are named an for some integer n >= 0

#theorems are interpreted as trees. [+, a, b] means a + b. [=, [., 1, a], a] means 1.a = a etc...

#theorems which only work one way go here - take care when substituting these 
#WIP
CORE = [[[">" ,"a0","a1"],["<" ,"a1","a0"]],
        [["<" ,"a0","a1"],[">" ,"a1","a0"]],
        [[">" ,"a0","a1"],[">" ,["+","a0","a2"],["+","a1","a2"]]]]

#equivalences go here - they can be substituted at any subtree
#most arithmetic rules added (except for / rules and ^ rules)
DEF = [[["+","a0","0"],"a0"],
       [[".","a0","1"],"a0"],
       [[".","a0",["+","a1","a2"]] ,["+",[".","a0","a1"],[".","a0","a2"]]],
       [["+" ,"a0", ["-", "a0"]],"0"],
       [["+","a1","a2"],["+","a2","a1"]],
       [[".","a1","a2"],[".","a2","a1"]],
       [["+","a0",["+","a1","a2"]],["+",["+","a0","a1"],"a2"]],
       [[".","a0",[".","a1","a2"]],[".",[".","a0","a1"],"a2"]]]


#coersion tries to apply theorem "template" to hypothesis "formula", and returns the necessary substitutions to get template from hypothesis,
# or return FALSE if formula cannot be coerced. Returns substitutions as a dictionary.
def coerce(formula,template):
   #if coercing onto symbol or function
   if template[0] != "a":
      #need to match
      if template[0] != formula[0]:
         return False
      else:
         #no point in continuing if input sizes differ
         if len(formula) != len(template):
            return False
         #coerce all subtrees
         dic = {}
         for i in range(1,len(template)):
            r = coerce(formula[i],template[i]) 
            #subtrees must be coerceable
            if r == False:
               return False
            #substitutions must match!
            for d in r:
               if d in dic:
                  if dic[d] != r[d]:
                     return False
               else:
                  dic.update({d: r[d]})
         #get substitution dictionary
         return dic
   else:
      #if coercing onto free variable then return formula
      return {template: formula}

#substitute dictionary of substitutions var_dict onto tree
def substitute(tree, var_dict):
    #if tree is not constant or free variable
    if isinstance(tree, list):
        #recursion
        return [substitute(node, var_dict) for node in tree]
    #else substitute free variable or leave constants
    elif tree in var_dict:
        return var_dict[tree]
    else:
        return tree
   
#find al subtrees of formula which coerce to eq[0], and replace with eq[1]
def sub_coercions(formula,eq):
   returnable = []
   full = coerce(formula,eq[0])
   if full != False and formula[0] not in sup:
      returnable.append(substitute(eq[1],full))
   if isinstance(formula, list):
      for j in range(1,len(formula)):
         result = sub_coercions(formula[j],eq)
         first = formula[0:j]
         last = formula[j:]
         last.pop(0)
         for i in result:
            returnable.append(first + [i] + last)
   return returnable

#WIP - format tree into readable equation
def format(S):
   try:
      s = S[0]
      if s in [">", "<", "=", "+", ".", "/", "^"]:
        return "(" + format(S[1]) + s + format(S[2]) + ")"
      elif s in ["a","0","1"]:
         return S
      else:
        return s + "(" + str(format(S[1]))  + ")"
   except:
      return str(S)

#Apply every possible equation and theorem to S, but remove results which can be coerced from "theory". Return new collection of theories"theory"
def run(S,theory):
   for law in CORE:
      result = coerce(S,law[0])
      if result != False:
         s = substitute(law[1],result)
         exists = False
         for t in theory:
            if coerce(s,t) != False:
               exists = True
               break
         if not exists:
            theory.append(s)
   for equation in DEF:
      for s in sub_coercions(S,equation):
         exists = False
         for t in theory:
            if coerce(s,t) != False:
               exists = True
               break
         if not exists:
            theory.append(s)
      for s in sub_coercions(S,[equation[1],equation[0]]):
         exists = False
         for t in theory:
            if coerce(s,t) != False:
               exists = True
               break
         if not exists:
            theory.append(s)
   return theory

#start from S, and apply every possible theorem and equation to S n times, and return list of theorems
def prove(S,n):
   theory = run(S[0],[])
   for i in range(n):
      Theory = theory.copy()
      for j in Theory:
         theory = run(j, theory)
   for s in theory:
      print(format(s))


prove(["=",[".","a0","0"],"0"],2)
