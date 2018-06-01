# -----------------------------------------------------------------------------
# calc.py
#
# A simple calculator with variables.
#
# Author : Guénin Vincent - Benard Alexis ESGI-3AL 2018
#
# If graphviz is a problem, install it, add it to your path and then launch
# your IDE in administrator mode
#
# -----------------------------------------------------------------------------

import ply.lex as lex
import ply.yacc as yacc
import uuid
import graphviz as gv
import re
import sys
from operator import xor
from time import strftime, time, gmtime

statement_counter = 1

tokens = (
    'AND', 'OR', 'TRUE', 'FALSE',
    'NAME', 'NUMBER',
    'PLUS', 'MINUS', 'TIMES', 'DIVIDE', 'MODULO', 'EQUALS',
    'IS_BIGGER', 'IS_BIGGER_EQUALS', 'IS_SMALLER', 'IS_SMALLER_EQUALS', 'IS_EQUALS', 'IS_DIFFERENT',
    'LPAREN', 'RPAREN', 'SEMICOLON', 'DOT',
    'IF', 'ELSE', 'END', 'AT', 'FOR', 'WHILE', 'ECHO',
    'STRING'
)

# Tokens
# Arithmetic operators
t_PLUS = r'\+'
t_MINUS = r'-'
t_TIMES = r'\*'
t_DIVIDE = r'/'
t_MODULO = r'\%'

# Comparison operators
t_IS_BIGGER = r'>'
t_IS_BIGGER_EQUALS = r'>='
t_IS_SMALLER = r'<'
t_IS_SMALLER_EQUALS = r'<='
t_IS_EQUALS = r'=='
t_IS_DIFFERENT = r'!='

# Boolean operators
t_AND = r'AND'
t_OR = r'OR'

# Assignment operator
t_EQUALS = r'='

# Syntax delimiters
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_SEMICOLON = r';'
t_AT = r'@'
t_DOT = r'\.'

# Function delimiters
t_IF = r'if'
t_ELSE = r'else'
t_END = r'end'
t_FOR = r'for'
t_WHILE = r'while'
t_ECHO = r'echo'

# Boolean values
t_TRUE = r'True'
t_FALSE = r'False'

# Variables
t_NAME = r'((?!(AND|OR|True|False|if|else|end|for|while|echo))([a-zA-Z_][a-zA-Z0-9_]*))'

# String
t_STRING = r'(\'[^\']*\'|"[^\"]*")'


def t_NUMBER(t):
    r"""\d+"""
    t.value = int(t.value)
    return t


# Ignored characters
t_ignore = " \t"


def t_newline(t):
    r"""\n+"""
    t.lexer.lineno += t.value.count("\n")


def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)


# Build the lexer
lex.lex()

# Precedence rules for the arithmetic operators
precedence = (
    ('left', 'PLUS', 'MINUS'),
    ('left', 'TIMES', 'DIVIDE'),
    ('right', 'UMINUS')
)

# -------------------- GRAMMAR RULES --------------------

# dictionary
names = {}
dict_comparison_operand = {'<', '<=', '>', '>=', '==', '!='}
dict_arithmetic_operand = {'+', '-', '*', '/', '%'}
dict_boolean_operand = {'AND', 'OR'}


# -------------------- PROGRAM --------------------
def p_program(p):
    """program : bloc"""
    p[0] = p[1]

    print(p[0])

    global write_in_compilation

    if write_in_compilation:
        begin_time = time()
        print_log("Compilation begin on " + strftime("%Y-%m-%d %H:%M:%S", gmtime(begin_time)) + " \n")
        print_log(p[0], string="program :")  # Affiche les statements

        eval_bloc(p[0])

        end_time = str(time() - begin_time).split('.')
        end_time = end_time[0] + '.' + end_time[1][:4]
        print_log("Compilation executed in %s seconds" % end_time)
    else:
        eval_bloc(p[0])

    # print_bloc_as_tree_in_command_line(p[0], 0, ' ')
    # print("names :", names)
    print_bloc_as_tree_in_graph(p[0])


# -------------------- BLOC --------------------
def p_bloc(p):
    """bloc : statement bloc
            | statement"""
    if len(p) == 3:
        p[0] = (p[1], p[2])
    else:
        p[0] = (p[1], ())


# -------------------- STATEMENT --------------------

def p_statement_expr(p):
    """statement : instruction SEMICOLON
                 | instruction"""
    p[0] = p[1]


# -------------------- INSTRUCTION --------------------

def p_instruction(p):
    """instruction : expression
                   | assignment
                   | iterative_exp
                   | echo_exp"""
    p[0] = p[1]


# -------------------- ECHO EXPRESSION --------------------

def p_echo_exp(p):
    """echo_exp : ECHO statement"""
    p[0] = ('echo', p[2])


# -------------------- EXPRESSION --------------------
def p_expression(p):
    """expression : boolean_exp
                  | arithmetic_exp
                  | conditional_exp"""
    p[0] = p[1]


# -------------------- BOOLEAN EXPRESSION --------------------
def p_boolean_exp(p):
    """boolean_exp : boolean_exp AND boolean_exp
                   | boolean_exp OR boolean_exp"""
    p[0] = (p[2], p[1], p[3])


def p_boolean_exp_variable(p):
    """boolean_exp : TRUE
                   | FALSE
                   | variable
                   | STRING"""
    p[0] = p[1]


def p_boolean_exp_comp(p):
    """boolean_exp : comparison_exp"""
    p[0] = p[1]


def p_boolean_exp_group(p):
    """boolean_exp : LPAREN boolean_exp RPAREN"""
    p[0] = p[2]


# -------------------- COMPARISON EXPRESSION --------------------
def p_comparison_exp(p):
    """comparison_exp : arithmetic_exp IS_BIGGER arithmetic_exp
                      | arithmetic_exp IS_BIGGER_EQUALS arithmetic_exp
                      | arithmetic_exp IS_SMALLER arithmetic_exp
                      | arithmetic_exp IS_SMALLER_EQUALS arithmetic_exp
                      | arithmetic_exp IS_EQUALS arithmetic_exp
                      | arithmetic_exp IS_DIFFERENT arithmetic_exp"""
    if type(p[1]) == bool or type(p[3]) == bool:
        error("Comparison operation impossible between type " + type(p[1]) + " and type " + type(p[3]))
    else:
        p[0] = (p[2], p[1], p[3])


def p_comparison_exp_group(p):
    """comparison_exp : LPAREN comparison_exp RPAREN"""
    p[0] = p[2]


# -------------------- ARITHMETIC EXPRESSION --------------------
def p_arithmetic_exp(p):
    """arithmetic_exp : arithmetic_exp PLUS arithmetic_exp
                      | arithmetic_exp MINUS arithmetic_exp
                      | arithmetic_exp TIMES arithmetic_exp
                      | arithmetic_exp DIVIDE arithmetic_exp
                      | arithmetic_exp MODULO arithmetic_exp"""
    if type(p[1]) == bool or type(p[3]) == bool:
        error("Arithmetic operation impossible between type " + type(p[1]) + " and type " + type(p[3]))
    else:
        p[0] = (p[2], p[1], p[3])


def p_arithmetic_exp_group(p):
    """arithmetic_exp : LPAREN arithmetic_exp RPAREN"""
    p[0] = p[2]


def p_arithmetic_exp_uminus(p):
    """arithmetic_exp : MINUS arithmetic_exp %prec UMINUS"""
    p[0] = -p[2]


# arithmetic_exp = STRING pour pouvoir faire "abc" * 3 => "abcabcabc"
def p_arithmetic_transform(p):
    """arithmetic_exp : num
                      | variable
                      | STRING"""
    p[0] = p[1]


# -------------------- NUMBER --------------------

def p_number(p):
    """num : NUMBER
           | float"""
    p[0] = p[1]


def p_float(p):
    """float : NUMBER DOT NUMBER"""
    p[0] = float(str(p[1]) + '.' + str(p[3]))


# -------------------- VARIABLE MANAGEMENT --------------------

def p_variable(p):
    """variable : NAME"""
    # p[0] = p[1]
    try:
        # p[0] = names[p[1]]
        p[0] = p[1]
    except LookupError:
        print("Undefined name '%s'" % p[1])
        p[0] = 0


def p_assignment(p):
    """assignment : NAME EQUALS expression"""
    p[0] = (p[2], p[1], p[3])
    # names[p[1]] = p[3]


# -------------------- CONDITIONAL EXPRESSION --------------------

def p_conditional_exp(p):
    """conditional_exp : IF boolean_exp AT bloc END
                       | IF boolean_exp AT bloc ELSE bloc END"""
    if len(p) == 6:
        p[0] = ('if', p[2], p[4])
    else:
        p[0] = ('if', p[2], p[4], p[6])


# -------------------- ITERATIVE EXPRESSION --------------------
def p_for_exp(p):
    """iterative_exp : FOR assignment AT boolean_exp AT bloc AT bloc END"""
    p[0] = ('for', p[2], p[4], p[6], p[8])


def p_for_exp_minimal(p):
    """iterative_exp : FOR assignment boolean_exp bloc AT bloc END"""
    p[0] = ('for', p[2], p[3], p[4], p[6])


def p_while_exp(p):
    """iterative_exp : WHILE boolean_exp AT bloc END"""
    p[0] = ('while', p[2], p[4])


def p_while_exp_minimal(p):
    """iterative_exp : WHILE boolean_exp bloc END"""
    p[0] = ('while', p[2], p[3])


# -------------------- ERROR --------------------

def p_error(p):
    print("Syntax error at '%s'" % p.value)


def error(string):
    print("Syntax error :", string)


# -------------------- CALCUL --------------------
def eval_bloc(bloc):
    global statement_counter

    if bloc == ():
        return

    if write_in_compilation:
        file_for_log = open('compilation.log', 'a')
        print("Statement number", statement_counter, ":", file=file_for_log)
        statement_counter = statement_counter + 1
        print_beautiful_dict(names, "names :", file_for_log)

        print('Evaluation :', str(bloc[0]), ':', str(eval_statement(bloc[0])), "\n\n", file=file_for_log)

        file_for_log.close()
    else:
        print(str(eval_statement(bloc[0])))

    eval_bloc(bloc[1])


def eval_statement(t):
    if type(t) != tuple:
        return eval_value(t)

    if t[0] in dict_arithmetic_operand:
        return eval_arithmetic_exp(t)
    elif t[0] in dict_comparison_operand:
        return eval_comparison_exp(t)
    elif t[0] in dict_boolean_operand:
        return eval_boolean_exp(t)
    elif t[0] == t_EQUALS:
        return eval_assignment_exp(t)
    elif t[0] == t_IF:
        return eval_conditional_exp(t)
    elif t[0] == t_FOR:
        return eval_for_exp(t)
    elif t[0] == t_WHILE:
        return eval_while_exp(t)
    elif t[0] == t_ECHO:
        return eval_echo_exp(t)
    else:
        print(t)
        return "Unknown command '" + t[0] + "'"


def eval_arithmetic_exp(t):
    if re.match(t_PLUS, t[0]):
        return eval_statement(t[1]) + eval_statement(t[2])
    if t[0] == t_MINUS:
        return eval_statement(t[1]) - eval_statement(t[2])
    if re.match(t_TIMES, t[0]):
        if xor(type(t[1]) == str, type(t[2]) == str):
            return eval_statement(t[1]) * eval_statement(t[2])
        else:
            return "Error operation '*' impossible between " + str(type(t[1])) + \
                   " and " + str(type(t[2]))
    if t[0] == t_DIVIDE:
        # Si une des deux variable est une string
        if type(t[1]) == str or type(t[1]) == str:
            return "Error : Cannot divide string"
        return eval_statement(t[1]) / eval_statement(t[2])
    if re.match(t_MODULO, t[0]):
        return eval_statement(t[1]) % eval_statement(t[2])
    else:
        return "An error has occurred, char '" + t[0] + "' unknown"


def eval_boolean_exp(t):
    if t[0] == t_AND:  # 'AND':
        return True if eval_statement(t[1]) and eval_statement(t[2]) else False
    if t[0] == t_OR:  # 'OR':
        return True if eval_statement(t[1]) or eval_statement(t[2]) else False


def eval_comparison_exp(t):
    if t[0] == t_IS_BIGGER:  # '>':
        return True if eval_statement(t[1]) > eval_statement(t[2]) else False
    elif t[0] == t_IS_BIGGER_EQUALS:  # '>=':
        return True if eval_statement(t[1]) >= eval_statement(t[2]) else False
    elif t[0] == t_IS_SMALLER:  # '<':
        return True if eval_statement(t[1]) < eval_statement(t[2]) else False
    elif t[0] == t_IS_SMALLER_EQUALS:  # '<=':
        return True if eval_statement(t[1]) <= eval_statement(t[2]) else False
    elif t[0] == t_IS_EQUALS:  # '==':
        return True if eval_statement(t[1]) == eval_statement(t[2]) else False
    elif t[0] == t_IS_DIFFERENT:  # '!=':
        return True if eval_statement(t[1]) != eval_statement(t[2]) else False


def eval_assignment_exp(t):
    val = eval_statement(t[2])
    names[t[1]] = val
    return str(t[1]) + ' <--- ' + str(val)


def eval_value(val):
    if val == t_TRUE:
        return True
    elif val == t_FALSE:
        return False
    elif type(val) == str:
        if val[0] == '\"' or val[0] == '\'':  # Si c'est une string
            return val[1:-1]
        else:  # Si c'est une variable
            # try:
            #    var = names[val]
            # except LookupError:
            #    print("Undefined name '%s'" % p[1])
            #    var = 0
            # return var
            return names[val]
    else:
        return val


def eval_conditional_exp(t):
    if eval_statement(t[1]):
        eval_bloc(t[2])
        return "If executed"
    else:
        if len(t) > 3:
            eval_bloc(t[3])
            return "Else executed"
    return "Condition in if was False"


def eval_for_exp(t):
    eval_statement(t[1])  # Assignment
    while eval_statement(t[2]):  # Boolean_exp
        eval_bloc(t[4])  # Treatments
        eval_bloc(t[3])  # Bloc in for
    return "For executed"


def eval_while_exp(t):
    while eval_statement(t[1]):
        eval_bloc(t[2])
    return "While executed"


def eval_echo_exp(t):
    res = str(eval_statement(t[1])) + " "
    print(res)
    return "echo executed"


# -------------------- DISPLAY --------------------

def get_decal(decal, car):
    res = ""
    for counter in range(0, decal):
        res = res + car
    return res


def print_bloc_as_tree_in_command_line(lst, decal, car, file_path=sys.stdout):
    for tple in lst:
        print_statement_as_tree_in_command_line(tple, decal, car, file_path)


def print_statement_as_tree_in_command_line(t, decal, car, file_path):
    res = get_decal(decal, car)
    if type(t) != tuple:
        print(res + str(t), file=file_path)
        return

    print(res + str(t[0]))
    print_statement_as_tree_in_command_line(t[1], decal + 1, car, file_path)
    print_statement_as_tree_in_command_line(t[2], decal + 1, car, file_path)


def print_bloc_as_tree_in_graph(tpl):
    graph = gv.Digraph(format='pdf')
    graph.attr('node', shape='circle')

    print_bloc_in_graph(graph, tpl)

    # for tple in lst:
    #     add_node(graph, tple)

    graph.render(filename="img/graph")  # Pour la sauvegarde du fichier
    # graph.view()


def print_statement_as_tree_in_graph(t):
    graph = gv.Digraph(format='pdf')
    graph.attr('node', shape='circle')
    add_node(graph, t)
    graph.render(filename='img/graph')  # Pour la sauvegarde du fichier
    # graph.view()  # Pour l'affichage du graph


def add_node(graph, t):
    my_id = uuid.uuid4()
    counter = 1

    if type(t) != tuple:
        graph.node(str(my_id), label=str(t))
        return my_id

    if t == ():
        return

    if type(t[0]) == tuple:
        for tpl in t:
            print(tpl)
            add_node(graph, tpl)
        return

    graph.node(str(my_id), label=str(t[0]))
    while counter < len(t):
        graph.edge(str(my_id), str(add_node(graph, t[counter])), arrowsize='0')
        counter += 1

    return my_id


def print_bloc_in_graph(graph, tpl, bloc_label='bloc', end_label='end'):
    my_id = uuid.uuid4()

    if tpl == ():
        graph.node(str(my_id), label=str(end_label))
        return my_id

    graph.node(str(my_id), label=str(bloc_label))
    graph.edge(str(my_id), str(print_statement_in_graph(graph, tpl[0])), arrowsize='0')
    graph.edge(str(my_id), str(print_bloc_in_graph(graph, tpl[1], bloc_label, end_label)), arrowsize='0')

    return my_id


def print_statement_in_graph(graph, tpl, bloc_label='bloc secondaire', end_label='end'):
    my_id = uuid.uuid4()

    if type(tpl) != tuple:  # Affiche les feuilles du graphe
        graph.node(str(my_id), label=str(tpl))
        return my_id

    if tpl == ():  # Fin d'un bloc
        return

    graph.node(str(my_id), label=str(tpl[0]))
    for counter in range(1, len(tpl)):
        if type(tpl[counter]) == tuple:
            if type(tpl[counter][0]) == tuple:
                bloc_son = print_bloc_in_graph(graph, tpl[counter], bloc_label, end_label)
                graph.edge(str(my_id), str(bloc_son), arrowsize='0')
                continue

        graph.edge(str(my_id), str(print_statement_in_graph(graph, tpl[counter])), arrowsize='0')

    return my_id


def print_beautiful_list(lst, string='', file_path=sys.stdout):
    print(string, '[', file=file_path)
    for el in lst:
        print('\t' + str(el) + ',', file=file_path)

    print(']\n', file=file_path)


def print_beautiful_dict(dct, string='', file_path=sys.stdout):
    print(string, '{', file=file_path)
    for index in dct:
        print('\t' + str(index) + ' : ' + str(dct[index]) + ',', file=file_path)

    print('}', file=file_path)


def print_log(something, string=''):
    if write_in_compilation:  # Si on écrit dans le fichier compilation.log
        file_to_write = open('compilation.log', 'a')
    else:
        file_to_write = sys.stdout

    if type(something) == dict:
        print_beautiful_dict(something, string=string, file_path=file_to_write)
    elif type(something) == list:
        print_beautiful_list(something, string=string, file_path=file_to_write)
    elif type(something) == tuple:
        print_statement_list(something, string=string, file_to_write_in=file_to_write)
    else:
        print(something, file=file_to_write)

    if write_in_compilation:
        file_to_write.close()


def print_statement_list(bloc, string='', file_to_write_in=sys.stdout):
    print(string, '(', file=file_to_write_in)
    print_statement(bloc, file_to_write_in)
    print(')', file=file_to_write_in)


def print_statement(bloc, file_to_write_in):
    if bloc == ():
        return

    print('\t' + str(bloc[0]), file=file_to_write_in)
    print_statement(bloc[1], file_to_write_in=file_to_write_in)


# -------------------- MAIN --------------------

yacc.yacc()
write_in_compilation = False  # False : On écrit dans la console - True : On écrit dans le fichier compilation.log

if len(sys.argv) >= 2:
    write_in_compilation = True
    log_file = open('compilation.log', 'w+')
    log_file.close()  # Clean the file

    file = open(sys.argv[1], 'r')
    content = file.read()
    file.close()

    yacc.parse(content)
else:
    while True:
        try:
            s = input('Oubliez pas les 2 points SVP > ')  # use input() on Python 3
            if s == "exit()":
                break
        except EOFError:
            break
        yacc.parse(s)
