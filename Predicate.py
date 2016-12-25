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