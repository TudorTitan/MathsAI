import numpy as np
from openai import OpenAI

client = OpenAI()

REL = [">", "<", "="] #relations
OP = ["+","-","*","/", "^"] #functions and operators
#all variables are named an for some integer n >= 0
#IDEA: an for positive integers, bn for integers, cn for rationals, dn for reals (Hierarchy)

#theorems are interpreted as trees. [+, a, b] means a + b. [=, [*, 1, a], a] means 1*a = a etc...

#Implications: the left and right parts of the tree contain further relations which cannot be evaluated to some number
                                                            # -so we cannot just substitute these anywhere
IMP = {"Symmetry for inequality relation": ["==",[">" ,"a0","a1"],["<" ,"a1","a0"]],
        "Add to both sides of inequality":["==",[">" ,"a0","a1"],[">" ,["+","a0","a2"],["+","a1","a2"]]],
        "Add to both sides of equality":["==",["=" ,"a0","a1"],["=" ,["+","a0","a2"],["+","a1","a2"]]]}

#Equivalences: left and right parts of the tree evaluate to some number
                             # - thus they can be substituted anywhere
EQ = {"Additive identity": ["=",["+","a0","0"],"a0"],
       "Multiplicative identity": ["=",["*","a0","1"],"a0"],
       "Distributivity": ["=",["*","a0",["+","a1","a2"]] ,["+",["*","a0","a1"],["*","a0","a2"]]],
       "Additive inverse": ["=",["+" ,"a0", ["-", "a0"]],"0"],
       "Symmetry of addition": ["=",["+","a1","a2"],["+","a2","a1"]],
       "symmetry of multiplication": ["=",["*","a1","a2"],["*","a2","a1"]],
       "associativity of addition": ["=",["+","a0",["+","a1","a2"]],["+",["+","a0","a1"],"a2"]],
       "associativity of multiplication": ["=",["*","a0",["*","a1","a2"]],["*",["*","a0","a1"],"a2"]]}

#a^2 - b^2 = (a+b)(a-b)
GOAL = ["=",["+", ["*","a","a"], ["-",["*","b","b"]]], ["*",["+","a","b"],["+","a",["-","b"]]]]

#coersion tries to apply theorem "template" to hypothesis "formula", and returns the necessary substitutions to get template from hypothesis,
# or return FALSE if formula cannot be coerced. Returns substitutions as a dictionary.
def coerce(formula,template):
   #if coercing onto symbol or function
   if template[0] not in ["a","b","c"]:
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

#Convert polish notation string into tree format
def polishToTree(string):
   print("POLISH " + string)
   tree = []
   polish = string.split(" ")
   for i in range(1,1+len(polish)):
      if polish[-i] == "-":
         u = tree[0]
         del tree[0]
         tree.insert(0,[polish[-i],u])
      elif polish[-i][0] not in ["a","b","c"]:
         u = tree[0]
         v = tree[1]
         del tree[0]
         del tree[0]
         tree.insert(0,[polish[-i],u,v])
      else:
         tree.insert(0,polish[-i])
   return(tree[0])

#Format tree into readable equation
def format(S):
   try:
      s = S[0]
      if s in [">", "<", "="]:
        return format(S[1]) + " " + s + " " + format(S[2])
      elif s == "+":
         if S[2][0] == "-":
            return "(" + format(S[1]) + " - " + format(S[2][1]) + ")"
         else:
            return "(" + format(S[1]) + " + " + format(S[2]) + ")"
      elif s in ["*", "/", "^"]:
         return "(" + format(S[1]) + s + format(S[2]) + ")"
      elif isinstance(S,str):
         return S
      else:
        return s + "(" + str(format(S[1]))  + ")"
   except:
      return str(S)

#Prove the goal given the hypothesis. Memory is the ChatGPT history and Steps are the number of steps left to apply
#Right now only works with EQ rules, still need to implement IMP rules
def prove(GOAL, Hypothesis, Memory, Steps):
   print("HYPOTHESIS " + format(Hypothesis))
   #There are two steps: First we apply a theorem and then we apply a substitution. All of math can be done this way
   #Form the prompt using the GOAL and hypothesis
   if Hypothesis == None:
      Prompt = "GOAL: " + format(GOAL) + ", HYPOTHESIS: None. Choose a rule to start from in order to prove the goal. This will become our next HYPOTHESIS. Write in the format RULE_NAME and nothing else! Adhere to this format or you will raise an error!!!"
   else:
      #Check if the goal is complete by trying to coerce hypothesis onto the goal
      if coerce(GOAL, Hypothesis) != False:
         return "FINISHED!"
      Prompt = "GOAL: " + format(GOAL) + ", HYPOTHESIS: " + format(Hypothesis) + ". Choose a rule to apply to the HYPOTHESIS. If there is more than one way to apply the rule, I will show you a list of options. Write in the format RULE_NAME and nothing else! Adhere to this format or you will raise an error!!!"
   #Apply prompt and update memory
   if Memory == None:
      Memory =  [{"role": "system", "content": "You are a mathematical theorem proving agent. I will write down a set of math rules which you are allowed to use. RULES: " + str({i:format(j) for i,j in EQ.items()}) + "," + str({i:format(j) for i,j in IMP.items()}) + ". I want to prove a GOAL, given a HYPOTHESIS. I will ask you which rule from RULES to apply to the HYPOTHESIS. If there is more than one way to apply the rule to the HYPOTHESIS, I will write down a list of possible options. You must choose which option is best in helping us solve the GOAL. After that I will ask you for a dictionary of substitutions to make to the HYPOTHESIS in preparation for the next rule to be applied. I will repeat this process until the GOAL can be achieved from the HYPOTHESIS by a substitution. Any symbol beginning with a letter is a free variable. To prove the goal, first apply additive inverse and then apply symmetry of addition"},{"role": "user","content": Prompt }]
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
   #Catch error from wrong format
   try:
      rule = EQ[rule]
   except:
      Memory = Memory + [{"role": "user","content": "Sorry but you did not write the rule in the format I asked for. Please write the rule name exactly as it was written in the dictonary RULES and nothing else!!!"}]
      response = client.chat.completions.create(
      model="gpt-3.5-turbo",
      messages=Memory)
      result = response.choices[0].message.content
      Memory = Memory + [{"role": "assistant","content": result }]
      rule = EQ[result]
   #Get options
   if Hypothesis == None:
      options = [rule]
   else:
      options = sub_coercions(Hypothesis,[rule[1],rule[2]]) + sub_coercions(Hypothesis,[rule[2],rule[1]])
   #Let ChatGPT choose from multiple options
   if len(options) > 1:
      Memory = Memory + [{"role": "user","content": "There are several possible ways to apply the rule. I will write down the options as a list. I want you to choose the option which helps us most in proving the goal. Return only the index of the option you want from this list, as an integer, and nothing else! Please adhere to this format!! Options: " + str([format(option) for option in options]) }]
      response = client.chat.completions.create(
         model="gpt-3.5-turbo",
         messages=Memory)
      result = response.choices[0].message.content
      Memory = Memory + [{"role": "assistant","content": result }]
      option = options[int(result)]
   elif len(options) == 1:
      option = options[0]
   else:
      #Fails to apply the rule
      #Restart (we can also potentially ask again)
      print("STUCK!")
      return prove(GOAL,None,None,Steps - 1)
   #Write option
   print("APPLY " + format(rule))
   print("RESULT " + format(option))
   Hypothesis = option
   if coerce(GOAL, Hypothesis) != False:
      return "FINISHED!"
   #Ask ChatGPT for a substitution
   Prompt = "GOAL: " + format(GOAL) + ", HYPOTHESIS: " + format(Hypothesis) + ". Write down a dictionary of substitutions to make into the HYPOTHESIS. Choose the substitutions which help us most in solving the GOAL. In doing so, think about which rule to apply next and what substitutions are required to make that rule applicable. Return in the format of a dictionary, where all formulas are in Polish notation! For example {a0: + a b, a1: * c d} will substitute a+b into a0 and c*d into a1. Make sure you adhere to this format otherwise you will generate an error!!!"
   Memory = Memory + [{"role": "user","content": Prompt }]
   response = client.chat.completions.create(
        model="gpt-3.5-turbo",
        messages=Memory)
   result = response.choices[0].message.content
   Memory = Memory + [{"role": "assistant","content": result }]
   #analyze ChatGPT recommendation
   rule = result
   #Catch format errors
   try: 
      subsList = [i.split(":") for i in rule.split("{")[1].split("}")[0].split(",")]
      print(subsList)
      Dict = {i[0].replace(" ", ""):polishToTree(i[1].strip()) for i in subsList}
      option = substitute(Hypothesis, Dict)
   except:
      Memory = Memory + [{"role": "user","content": "Sorry but you did not write the substitution in the format I asked for. Please return as a dictionary and make sure all formulas are in Polish notation!!! An example of a valid format is {a0: + a b, a1: * c d} which will substitute a+b into a0 and c*d into a1."}]
      response = client.chat.completions.create(
      model="gpt-3.5-turbo",
      messages=Memory)
      result = response.choices[0].message.content
      rule = result
      Memory = Memory + [{"role": "assistant","content": result }]
      subsList = [i.split(":") for i in rule.split("{")[1].split("}")[0].split(",")]
      print(subsList)
      Dict = {i[0].replace(" ", ""):polishToTree(i[1].strip()) for i in subsList}
      option = substitute(Hypothesis, Dict)
   print("SUBSTITUTE " + str(Dict))   
   print("RESULT " + format(option))
   if Steps <= 1:
      return "OUT OF STEPS!"
   else:
      return prove(GOAL,option,Memory,Steps - 1)

#print(prove(GOAL, None, None,3))  
