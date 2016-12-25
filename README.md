# FOL-Resolution
Implements inference using Resolution, a prove by contradiction approach for First Order Logic Statements
<br>
# Resolution
Resolution is a method of inference leading to a refutation theorem-proving technique for sentences in propositional logic and first-order logic(FOL). In other words, iteratively applying the resolution rule along with unification in a suitable way allows for inferencing whether a FOL statement is satisfiable or unsatisfiable. Attempting to prove a satisfiable FOL statement as unsatisfiable may result in a nonterminating computation; this problem doesn't occur in propositional logic. Resolution works on statemets in Conjunctive Normal Form(CNF) and hence FOL statements are first converted to CNF. Resolution is a complete and sound inference procedure because it works on CNF which is universal.
<br>
# Steps involved:
The overview of the whole process is as follows:<br>
1. FOL Statements of Knowledge base are first converted to CNF<br>
2. One query is picked at a time, it is negated and added to Knowledge base<br>
3. Resolution inference is applied using the method of Set of Sets to prove the query by inferencing a contradiction.<br>
<br>
The steps involved in FOL to CNF conversion are:<br>
1. Replace predicate strings in a statement by a string constant.<br>
2. Convert the infix statement to postfix using Shunting-Yard Algorithm.<br>
3. Convert postfix statement to expression tree.<br>
4. Remove implication from statement.<br>
5. Propogate negation inside the statement.<br>
6. Distribute And over Or.<br>
7. Perform inorder traversal of expression tree to get the CNF statement string.<br>
8. Split statements on And operator.<br>
9. Standardize the variables of each CNF statement.<br>
<br>
# How to execute:
Make sure Resolution.py and input.txt are in the same directory before running the script file. When you run the Resolution.py file, it reads input.txt and applies FOL to CNF conversion steps and performs resoltion to prove the queries. The script generates output.txt which contains the True/False output for each query. True if a query can be infered from the Knowledge base and False if it cannot be.<br>
# Input Format:
&lt;NUMBER OF QUERIES&gt;<br>
&lt;QUERY 1&gt;<br>
...<br>
&lt;QUERY n&gt;<br>
&lt;NUMBER OF FOL SENTENCES IN THE KNOWLEDGE BASE&gt;<br>
&lt;FOL SENTENCE 1&gt;<br>
...<br>
&lt;FOL SENTENCE m&gt;<br>
<br>
# Output Format:
For each query, the output denotes if that query can be inferred from the knowledge base or not, one query per line:<br>
&lt;ANSWER 1&gt;<br>
...<br>
&lt;ANSWER n&gt;<br>
where,<br>
each answer is either TRUE if it can be proved given the knowledge base, or FALSE if it cannot be.<br>
<br>
# Runner:
You can test the script on multiple Knowledge bases present in cases directory using the Runner.py utility, Make sure you keep the 'cases' directory at the same level as Runner.py and Resolution.py
