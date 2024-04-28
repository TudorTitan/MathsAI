import numpy as np
from openai import OpenAI

client = OpenAI()

REL = [">", "<", "="] #relations
OP = ["+","-",".","/", "^"] #functions and operators
#all variables are named an for some integer n >= 0
#IDEA: an for positive integers, bn for integers, cn for rationals, dn for reals (Hierarchy)

#theorems are interpreted as trees. [+, a, b] means a + b. [=, [., 1, a], a] means 1.a = a etc...

#Implications: the left and right parts of the tree contain further relations which cannot be evaluated to some number
                                                            # -so we cannot just substitute these anywhere
IMP = {"Symmetry for inequality relation": ["==",[">" ,"a0","a1"],["<" ,"a1","a0"]],
        "Add to both sides of inequality":["==",[">" ,"a0","a1"],[">" ,["+","a0","a2"],["+","a1","a2"]]],
        "Add to both sides of equality":["==",["=" ,"a0","a1"],["=" ,["+","a0","a2"],["+","a1","a2"]]]}

#Equivalences: left and right parts of the tree evaluate to some number
                             # - thus they can be substituted anywhere
#most arithmetic rules added (except for / rules and ^ rules)
EQ = {"Additive identity": ["=",["+","a0","0"],"a0"],
       "Multiplicative identity": ["=",[".","a0","1"],"a0"],
       "Distributivity": ["=",[".","a0",["+","a1","a2"]] ,["+",[".","a0","a1"],[".","a0","a2"]]],
       "Additive inverse": ["=",["+" ,"a0", ["-", "a0"]],"0"],
       "Symmetry of addition": ["=",["+","a1","a2"],["+","a2","a1"]],
       "symmetry of multiplication": ["=",[".","a1","a2"],[".","a2","a1"]],
       "associativity of addition": ["=",["+","a0",["+","a1","a2"]],["+",["+","a0","a1"],"a2"]],
       "associativity of multiplication": ["=",[".","a0",[".","a1","a2"]],[".",[".","a0","a1"],"a2"]]}

GOAL = ["=",["+", ["*","a","a"], ["-",["*","b","b"]]], ["*",["+","a","b"],["+","a",["-","b"]]]]

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
   
#find all subtrees of formula which coerce to eq[0], and replace with eq[1]
def sub_coercions(formula,eq):
   #there are multiple possibilities so we will return them all as this list
   returnable = []
   #try to coerce formula to eq[0]
   full = coerce(formula,eq[0])
   if full != False and formula[0] not in REL:
      returnable.append(substitute(eq[1],full))
   if isinstance(formula, list):
      for j in range(1,len(formula)):
         #use recursion, get a list of coercions of subtree
         result = sub_coercions(formula[j],eq)
         first = formula[0:j]
         last = formula[j:]
         last.pop(0)
         for i in result:
            returnable.append(first + [i] + last)
   return returnable

#Format tree into readable equation
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

#start from S, and apply every possible theorem and equation to S n times, and return list of theorems
def prove(GOAL, Hypothesis, Memory, Steps):
   #form the prompt using the GOAL and hypothesis
   if Hypothesis == None:
      Prompt = "I want to prove the goal, and there is a list of rules which I can apply. These are all described as trees, where any symbol beginning with a letter is a free variable. State the best rule to start from in my proof. Return in the format [RULE NAME] without the square brackets. Return only this and nothing else! Goal: " + str(GOAL) + ", Rules: " + str(EQ) + "," + str(IMP)
   else:
      Prompt = "I want to prove the goal given the hypothesis and rules which I can apply. These are all described as trees, where any symbol beginning with a letter is a free variable. State the best rule to apply to the hypothesis to help us prove the goal. Return in the format [RULE NAME] without the square brackets. Return only this and nothing else! Goal: " + str(GOAL) + ", Hypothesis: " + str(Hypothesis) + ", Rules: " + str(EQ) + "," + str(IMP)
   #Apply prompt and update memory
   if Memory == None:
      Memory =  [{"role": "system", "content": "You are a helpful assistant."},{"role": "user","content": Prompt }]
      response = client.chat.completions.create(
        model="gpt-3.5-turbo",
        messages=Memory)
      result = response.choices[0].message.content
   else:
      Memory = Memory + [{"role": "user","content": Prompt }]
      response = client.chat.completions.create(
        model="gpt-3.5-turbo",
        messages=Memory)
      result = response.choices[0].message.content
   Memory = Memory + [{"role": "assistant","content": result }]
   #analyze ChatGPT recommendation
   rule = result
   rule = EQ[rule]
   if Hypothesis == None:
      options = [rule]
   else:
      options = sub_coercions(Hypothesis,[rule[1],rule[2]]) + sub_coercions(Hypothesis,[rule[2],rule[1]])
   #let ChatGPT choose from multiple options
   if len(options) > 1:
      Memory = Memory + [{"role": "user","content": "There are several possible ways to apply the rule. I will write down the options as a list. I want you to choose the application which helps us most in proving the goal. Return only the index of the option as an integer and nothing else. Options: " + str(options) }]
      response = client.chat.completions.create(
        model="gpt-3.5-turbo",
        messages=Memory)
      result = response.choices[0].message.content
      Memory = Memory + [{"role": "assistant","content": result }]
      option = options[int(result)]
   elif len(options) == 1:
      option = options[0]
   else:
      #fails
      print("STUCK!")
      return prove(GOAL,None,None,Steps - 1)
   print(option)
   if Steps == 1:
      return "DONE!"
   else:
      return prove(GOAL,option,Memory,Steps - 1)

print(prove(GOAL, None, None,10))
