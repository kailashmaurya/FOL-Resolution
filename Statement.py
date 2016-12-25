from Predicate import *
import copy

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