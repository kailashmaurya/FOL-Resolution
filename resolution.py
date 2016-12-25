import re
import copy
UPPER_ALPHA_MAPPING = ['A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P','Q','R','S','T','U','V','W','X','Y','Z']
LOWER_ALPHA_MAPPING = ['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v','w','x','y','z']
OPERATOR_PRIORITY = {'~':4, '&':3, '|':2, '=>':1}       #~: Not, &: And, |: Or, =>: Implication
traversal = ''
predicates_dict = {}            #maintains predicates to constant mapping for a FOL statement
STANDARD_VARIABLE_COUNT = 0     #maintains a count of standardized variables 
TRUE = 'TRUE'
FALSE = 'FALSE'
INPUT_FILE = 'input.txt'
OUTPUT_FILE = 'output.txt'
KILL_LIMIT = 8000               #kills the resolution inference when Knowledge base size exceeds KILL_LIMIT
KNOWLEDGE_BASE_HASH = {}
KNOWLEDGE_BASE = set()
"""
Structure of KNOWLEDGE_BASE_HASH:
{
    "Predicate_Name" : set(statement_1, statement_2 ...) - that is set of statements objects
}

Structure of KNOWLEDGE_BASE:
set([
    Statement Object 1,
    Statement Object 2,
    ...
])
"""

class Node():
    """
    An object of this class is used to hold one predicate
    of a statement, used to construct a statement tree
    while parsing a statement and converting it to CNF.
    """
    def __init__(self, value):
        self.value = value
        self.negation = False
        self.operator = True
        self.left = None
        self.right = None
        if value in predicates_dict:
            if '~' in predicates_dict[value]:
                self.negation = True
                predicates_dict[value] = predicates_dict[value][1:]
            self.operator = False

class Predicate():
    """
    defines one predicate and the operations allowed on them
    member variables include:
    negative : True if predicate is negated
    name : the name of the predicate
    predicate_string : the unparsed predicate string
    arguments : list of predicate arguments
    """
    def __init__(self, predicate):
        """
        predicate should be of the form : ~A(x,y,John)
        negative : True if predicate is negated
        name : predicate name
        arguments : list of arguments
        """
        split_predicate = predicate.split('(')
        self.negative = False
        self.name = split_predicate[0]
        self.predicate_string = predicate
        if '~' in split_predicate[0]:
            self.name = split_predicate[0][1:]
            self.negative = True
        parameters = split_predicate[1][:-1]        # remove closing parenthesis
        self.arguments = parameters.split(',')
        variable_prefix = self.name[0].lower()

    def __str__(self):
        return '~'[not self.negative:] + self.name + '(' + ','.join(self.arguments) + ')'

    def negate(self):
        """
        to negate a predicate
        """
        self.negative = not self.negative
        self.update_predicate_string()

    def __eq__(self, predicate):
        return self.__dict__ == predicate.__dict__

    def __hash__(self):
        return hash((self.predicate_string))

    def unify_with_predicate(self, predicate):
        """
        returns substitution if the self predicate object
        unifies successfully with predicate argument else 
        returns False if cannot be unified
        """
        if self.name == predicate.name and len(self.arguments) == len(predicate.arguments):
            substitution = {}
            return unify(self.arguments, predicate.arguments, substitution)
        else:
            return False

    def update_predicate_string(self):
        """
        reconstructs predicate string
        """
        self.predicate_string = '~'[not self.negative:] + self.name + '(' + ','.join(self.arguments) + ')'

    def substitute(self, substitution):
        """
        substitues 'substitution' in the self predicate 
        object obtained as a result of unification of 
        this predicate with another
        """
        if substitution:
            for index, arg in enumerate(self.arguments):
                if arg in substitution:
                    self.arguments[index] = substitution[arg]
            self.update_predicate_string()
        return self

class Statement():
    """
    defines one FOL statement and the operations allowed on them
    member variables include:
    predicate_set : set of 'Predicate' objects which are 
    connected via OR operator in a statement
    statement_string : string representation of statement
    """
    def __init__(self, statement_string=None):
        if statement_string:
            predicate_list = statement_string.split('|')
            predicate_list = map(lambda x:Predicate(x), predicate_list)
            self.predicate_set = set(predicate_list)
            statement_string_list = map(lambda x: x.predicate_string, self.predicate_set)
            self.statement_string = '|'.join(statement_string_list)
        else:
            self.statement_string = None
            self.predicate_set = None

    def init_from_string(self, statement_string):
        """
        initializes a Statement object from statement string
        """
        predicate_list = statement_string.split('|')
        predicate_list = map(lambda x:Predicate(x), predicate_list)
        self.predicate_set = set(predicate_list)
        statement_string_list = map(lambda x: x.predicate_string, self.predicate_set)
        self.statement_string = '|'.join(statement_string_list)

    def init_from_predicate_set(self, predicate_set):
        """
        initializes Statement object from a predicate set
        """
        self.predicate_set = predicate_set
        statement_string_list = map(lambda x: x.predicate_string, predicate_set)
        self.statement_string = '|'.join(statement_string_list)

    def __str__(self):
        return self.statement_string

    def __eq__(self, statement):
        return self.predicate_set==statement.predicate_set

    def __hash__(self):
        return hash((''.join(sorted(self.statement_string))))

    def exists_in_KB(self, KB):
        '''
        returns true if cnf_statement already exists
        in the KNOWLEDGE_BASE else False
        '''
        if self in KB:
            return True
        return False

    def add_statement_to_KB(self, KB, KB_HASH):
        """
        adds a statement in a knowledge base and updates the Hash
        """
        KB.add(self)
        for predicate in self.predicate_set:
            if predicate.name in KB_HASH:
                KB_HASH[predicate.name].add(self)
            else:
                KB_HASH[predicate.name] = set([self])

    def resolve(self, statement):
        '''
        Resolves two statements
        returns False if a contradiction is encountered when resolved otherwise,
        returns set of new infered statements(empty if no statements infered)
        '''
        infered_statements = set()
        for predicate_1 in self.predicate_set:
            for predicate_2 in statement.predicate_set:
                unification = False
                if (predicate_1.negative ^ predicate_2.negative) and predicate_1.name==predicate_2.name:
                    unification = predicate_1.unify_with_predicate(predicate_2) # returns substitution if statements can unify else false
                if unification == False:
                    continue
                else:
                    rest_statement_1 = copy.deepcopy(self.predicate_set)
                    rest_statement_2 = copy.deepcopy(statement.predicate_set)
                    rest_statement_1 = filter(lambda x: False if x == predicate_1 else True, rest_statement_1)
                    rest_statement_2 = filter(lambda x: False if x == predicate_2 else True, rest_statement_2)
                    if not rest_statement_1 and not rest_statement_2:           # contradiction found
                        return False
                    rest_statement_1 = map(lambda x: x.substitute(unification), rest_statement_1)
                    rest_statement_2 = map(lambda x: x.substitute(unification), rest_statement_2)
                    new_statement = Statement()
                    new_statement.init_from_predicate_set(set(rest_statement_1+rest_statement_2))
                    infered_statements.add(new_statement)
        return infered_statements

    def get_resolving_clauses(self, KB_HASH):
        """
        returns a set of possible statements
        the self statement object can resolve with
        """
        resolving_clauses = set()
        for predicate in self.predicate_set:
            if predicate.name in KB_HASH:
                resolving_clauses = resolving_clauses.union(KB_HASH[predicate.name])
        return resolving_clauses
        

def unify(predicate1_arg, predicate2_arg, substitution):
    """
    unifies two predicates and returns the substitution
    returns false if predicates cannot be unified
    """
    if substitution == False:
        return False
    elif predicate1_arg == predicate2_arg:
        return substitution
    elif isinstance(predicate1_arg, str) and predicate1_arg.islower():
        return unify_var(predicate1_arg, predicate2_arg, substitution)
    elif isinstance(predicate2_arg, str) and predicate2_arg.islower():
        return unify_var(predicate2_arg, predicate1_arg, substitution)
    elif isinstance(predicate1_arg, list) and isinstance(predicate2_arg, list):
        if predicate1_arg and predicate2_arg:
            return unify(predicate1_arg[1:], predicate2_arg[1:], unify(predicate1_arg[0], predicate2_arg[0], substitution))
        else:
            return substitution
    else:
        return False

def unify_var(var, x, substitution):
    if var in substitution:
        return unify(substitution[var], x, substitution)
    elif x in substitution:
        return unify(var, substitution[x], substitution)
    else:
        substitution[var] = x
        return substitution


def inorder_traversal(node):
    global traversal
    traversal = ''
    inorder(node)
    return traversal

def inorder(node):
    global traversal
    if node:
        inorder(node.left)
        if node.negation:
            traversal += '~' + node.value
        else:
            traversal += node.value
        inorder(node.right)

def give_constant(count, uppercase):
    '''
    count >= 0
    uppercase : if True then constant begin from AA, else from aa
    returns a string constant for count value
    '''
    start = count + 26
    str_constant = ''
    while start >= 26:
        val = start % 26
        if uppercase:
            str_constant = UPPER_ALPHA_MAPPING[val] + str_constant
        else:
            str_constant = LOWER_ALPHA_MAPPING[val] + str_constant
        start //= 26
    if uppercase:
        str_constant = UPPER_ALPHA_MAPPING[start-1] + str_constant
    else:
        str_constant = LOWER_ALPHA_MAPPING[start-1] + str_constant
    return str_constant

def distribute_and_over_or(node):
    """
    distributes and over or in the step
    of converting an FOL statement to CNF
    """
    if node:
        if node.value == '|':
            if node.left.value == '&' and node.right.value == '&':      # OR as parent, two AND as its children
                left_and = node.left
                right_and = node.right
                a = left_and.left
                b = left_and.right
                c = right_and.left
                d = right_and.right
                a_copy = copy.deepcopy(a)
                b_copy = copy.deepcopy(b) 
                c_copy = copy.deepcopy(c)
                d_copy = copy.deepcopy(d)
                left_or_1 = Node('|')
                left_or_2 = Node('|')
                right_or_1 = Node('|')
                right_or_2 = Node('|')
                node.value = '&'
                left_and.left = left_or_1
                left_and.right = left_or_2
                right_and.left = right_or_1
                right_and.right = right_or_2
                left_or_1.left = a
                left_or_1.right = c
                left_or_2.left = a_copy
                left_or_2.right = d
                right_or_1.left = b
                right_or_1.right = c_copy
                right_or_2.left = b_copy
                right_or_2.right = d_copy
            elif node.left.operator and not node.right.operator and node.left.value == '&':
                c = node.left.right
                a = node.right
                a_copy = copy.deepcopy(a)
                right_or = Node('|')
                node.value = '&'
                node.left.value = '|'
                node.left.right = a
                node.right = right_or
                right_or.left = c
                right_or.right = a_copy
            elif not node.left.operator and node.right.operator and node.right.value == '&':
                a = node.left
                a_copy = copy.deepcopy(a)
                b = node.right.left
                left_or = Node('|')
                node.value = '&'
                node.right.value = '|'
                node.left = left_or
                left_or.left = a
                left_or.right = b
                node.right.left = a_copy
        distribute_and_over_or(node.left)
        distribute_and_over_or(node.right)

def propagate_negation(node):
    """
    moves negation inside and hence applies De Morgans law
    """
    if node:
        if node.operator and node.negation:
            node.left.negation = not node.left.negation
            node.right.negation = not node.right.negation
            if node.value == '&':
                node.value = '|'
            else:
                node.value = '&'
            node.negation = False
        propagate_negation(node.left)
        propagate_negation(node.right)

def remove_implication(node):
    """
    A=>B is equivalent to ~A|B
    thus this method performs implication removal
    """
    if node:
        remove_implication(node.left)
        if node.operator and node.value == '=>':
            node.value = '|'
            node.left.negation = not node.left.negation
        remove_implication(node.right)        

def convert_postfix_to_tree(statement):
    """
    parses postfix representation of a statement and
    converts it to tree notation, where leaf nodes 
    are predicate nodes and internal nodes are operators
    """
    stack = []
    r = re.compile('(~|&|\||=>|[A-Z][A-Z])')
    predicates = r.findall(statement)
    for token in predicates:
        if token in ['&', '|', '=>']:
            operand2 = stack.pop()
            operand1 = stack.pop()
            operator = Node(token)
            operator.left = operand1
            operator.right = operand2
            stack.append(operator)
        elif token == '~':
            stack[-1].negation = not stack[-1].negation
        else:
            operand = Node(token)
            stack.append(operand)
    return stack[0]

def convert_to_postfix(statement):
    """
    implementation of Shunting-Yard Algorithm
    to convert a infix statement to postfix statement
    """
    stack = []
    r = re.compile('(~|&|\||=>|[A-Z][A-Z]|\(|\))')
    predicates = r.findall(statement)
    postfix = ''
    for token in predicates:
        if re.match('[A-Z][A-Z]', token):
            postfix += token
        elif token in ['~', '&', '|', '=>']:
            while len(stack) != 0 and stack[-1] not in ['(', ')'] and OPERATOR_PRIORITY[stack[-1]] >= OPERATOR_PRIORITY[token]:
                postfix += stack.pop()
            stack.append(token)
        elif token == '(':
            stack.append(token)
        elif token == ')':
            while stack[-1] != '(':
                postfix += stack.pop()
            stack.pop()
    while stack:
        postfix += stack.pop()
    return postfix

def replace_predicate_by_constant(statement):
    """
    replaces a predicate string by a string 
    constant of length 2, for easy parsing
    ex: Mother(x,y) can be replaced by AB
    """
    r = re.compile('~?[A-Z][A-Za-z]*\([a-zA-Z][a-zA-Z,]*\)')
    predicates = r.findall(statement)
    predicates_dict = {}
    for index, predicate in enumerate(set(predicates)):
        predicate_constant = give_constant(index, True)
        predicates_dict[predicate_constant] = predicate
        statement = statement.replace(predicate, predicate_constant)
    return statement, predicates_dict
    
def replace_constant_by_predicate(statement, predicates_dict):
    """
    restores predicate string in place of constants 
    for getting the original statement back
    """
    for key, value in predicates_dict.iteritems():
        statement = statement.replace(key, value)
    return statement

def standardize_variables(statements):
    '''
    takes list of CNF statements strings as argument 
    return them as list of standardized CNF statements,
    standardizes the variables for all the statements
    '''
    global STANDARD_VARIABLE_COUNT
    standard_statements = []
    for statement in statements:
        variable_dict = {}
        r = re.compile('\([a-zA-Z,]+\)')
        parameters = r.findall(statement)
        parameters = map(lambda x:x[1:-1], parameters)
        parameters = ','.join(parameters)
        parameters = parameters.split(',')
        parameters = filter(lambda x: x.islower(), parameters)
        parameters = list(set(parameters))
        for para in parameters:
            variable_dict[para] = give_constant(STANDARD_VARIABLE_COUNT, False)
            STANDARD_VARIABLE_COUNT += 1
        predicates = statement.split('|')
        predicate_list = []
        for predicate in predicates:
            parts = predicate.split('(')
            parameters = parts[1][:-1].split(',')
            parameters = map(lambda x:variable_dict[x] if x in variable_dict else x, parameters)
            predicate = parts[0] + '(' + ','.join(parameters) + ')'
            predicate_list.append(predicate)
        standard_statements.append('|'.join(predicate_list))
    return standard_statements
            

def init_problem():
    """
    Parses the Query statements and the Knowledge base
    statements from the input file and returns them
    """
    QUERIES = []
    FOL_SENTENCES = []
    with open(INPUT_FILE) as f_input:
        file = list(f_input)
    f_input.close()
    NO_OF_QUERIES = int(file[0].rstrip('\n'))
    for query_line in file[1:1+NO_OF_QUERIES]:
        query_line = query_line.rstrip()
        query_line = query_line.replace(' ','')
        query_line = query_line.replace('\t','')
        QUERIES.append(Predicate(query_line))
    NO_OF_FOL_SENTENCES = int(file[1+NO_OF_QUERIES].rstrip('\n'))
    for fol_sentence in file[2+NO_OF_QUERIES:2+NO_OF_QUERIES+NO_OF_FOL_SENTENCES]:
        fol_sentence = fol_sentence.rstrip()
        fol_sentence = fol_sentence.replace(' ', '')
        fol_sentence = fol_sentence.replace('\t', '')
        FOL_SENTENCES.append(fol_sentence)
    FOL_SENTENCES = list(set(FOL_SENTENCES))
    return QUERIES, FOL_SENTENCES

def prepare_knowledgebase(FOL_SENTENCES):
    """
    Takes a set of FOL statements and performs 
    preprocessing for converting them to CNF form
    adds the converted CNF statements to KNOWLEDGE_BASE and 
    updates the KNOWLEDGE_BASE_HASH
    """
    global predicates_dict
    for statement in FOL_SENTENCES:
        predicates_dict.clear()
        statement, predicates_dict = replace_predicate_by_constant(statement)
        statement = convert_to_postfix(statement)
        root = convert_postfix_to_tree(statement)               # convert to expression tree
        remove_implication(root)                                # remove implication
        propagate_negation(root)                                # propagate negation
        distribute_and_over_or(root)                            # distribute AND over OR
        inorder = inorder_traversal(root)
        statement = replace_constant_by_predicate(inorder, predicates_dict)
        statements = statement.split('&')
        statements = standardize_variables(statements)
        for cnf_stmt in statements:
            stmt_obj = Statement(cnf_stmt)
            stmt_obj.add_statement_to_KB(KNOWLEDGE_BASE, KNOWLEDGE_BASE_HASH)

def display_knowledgebase(KB, KB_HASH=None):
    """
    takes Knowledge base and KNOWLEDGE_BASE_HASH as arguments
    """
    print "\nKNOWLEDGE_BASE\n"
    for statement in KB:
        print statement
    print 'Total No. of Statements : ', len(KB)
    if KB_HASH:
        print "\nKNOWLEDGE_BASE_HASH\n"
        for key, value in KB_HASH.iteritems():
            print key, ':', len(value), ' Statements'
    
def FOL_Resolution(KB, KB_HASH, query):
    """
    Performs resolution of KB and query using Set of Set
    approach where KB is one set and KB2 is the second set
    query is the statement to be proved using resolution
    Returns: True if a contradiction is found and hence query 
    is proved to be True
    else False if query cannot be proved from the Knowledge base
    """
    KB2 = set()
    KB_HASH = {}
    query.add_statement_to_KB(KB2, KB_HASH)
    query.add_statement_to_KB(KB, KB_HASH)
    while True:
        history = {}        # maintains mapping of statements that have been resolved earlier
        new_statements = set()
        # stop resoltion if Knowledge base size grows more than KILL_LIMIT
        if len(KB) > KILL_LIMIT: return False
        for statement1 in KB:
            # get possible set of statements with which the current statement cant be resolved
            resolving_clauses = statement1.get_resolving_clauses(KB_HASH)
            for statement2 in resolving_clauses:
                if statement1 == statement2:
                    continue        # avoids resolution of a statement with itself
                flag1 = False
                flag2 = False
                if statement2.statement_string in history:
                    flag1 = True
                    if statement1.statement_string in history[statement2.statement_string]:
                        history[statement2.statement_string].discard(statement1.statement_string)
                        continue        # avoids resolving two statements that appear in history
                if statement1.statement_string in history:
                    flag2 = True
                    if statement2.statement_string in history[statement1.statement_string]:
                        history[statement1.statement_string].discard(statement2.statement_string)
                        continue        # avoids resolving two statements that appear in history
                # update history
                if flag2:
                    history[statement1.statement_string].add(statement2.statement_string)
                else:
                    history[statement1.statement_string] = set([statement2.statement_string])
                resolvents = statement1.resolve(statement2)     # resolve statement1 with statement2
                if resolvents == False:             #contradiction found, return True
                    return True
                new_statements = new_statements.union(resolvents)
        if new_statements.issubset(KB):
            return False    # returns False if no new Knowledge is infered
        new_statements = new_statements.difference(KB)
        # update Knowledge base 2 to contains newly infered statements only
        KB2 = set()
        KB_HASH = {}
        for stmt in new_statements:
            stmt.add_statement_to_KB(KB2, KB_HASH)
        # add newly infered statements to Knowledge base 1 as well
        # to allow resoltion between newly infered statements
        KB = KB.union(new_statements)
    
def write_output(result):
    """
    writes output of a query to OUTPUT_FILE
    """
    output = TRUE + '\n' if result else FALSE + '\n'
    with open(OUTPUT_FILE, 'a') as f_output:
        f_output.write(output)
    f_output.close()

def factor_statements(statement_set):
    """
    removes duplicate predicates from a set 
    of statements and returns factored statements    
    """
    for statement in statement_set:
        new_predicate_set = set()
        predicate_list = list(statement.predicate_set)
        for index, predicate1 in enumerate(predicate_list):
            for predicate2 in predicate_list[index+1:]:
                if predicate1.negative == predicate2.negative:
                    substitution = predicate1.unify_with_predicate(predicate2)
                    if substitution == False:
                        continue
                    else:
                        for pred in predicate_list:
                            pred.substitute(substitution)
        statement.init_from_predicate_set(set(predicate_list))
    return statement_set

QUERIES, FOL_SENTENCES = init_problem()
prepare_knowledgebase(FOL_SENTENCES)
# performs resolution for each query
# negates the query, prepares a statement for the negated query, 
# prepares a new copy of Knowledge base and Hash
# Performs resoltion and writes result
for query_predicate in QUERIES:
    query_predicate.negate()
    query_predicate = Statement(query_predicate.predicate_string)
    KB = copy.deepcopy(KNOWLEDGE_BASE)
    KB_HASH = copy.deepcopy(KNOWLEDGE_BASE_HASH)
    satisfiability = FOL_Resolution(KB, KB_HASH, query_predicate)
    write_output(satisfiability)