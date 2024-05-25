-------------- MODULE batalha --------------
EXTENDS Integers, Sequences, SequencesExt, TLC

VARIABLES criaturas, proximo, round, ordemDeAtaque, ultimoAtaque, inicializado

CONSTANTS Mago, Clerigo, Barbaro, Monstro

CRIATURAS == [
  Mago    |-> [classe |-> "mago", hp |-> 20, tipo |-> "personagem", paralisia |-> FALSE, imunidade |-> FALSE, iniciativa |-> 0],
  Clerigo |-> [classe |-> "clerigo", hp |-> 20, tipo |-> "personagem", paralisia |-> FALSE, imunidade |-> FALSE, iniciativa |-> 0],
  Barbaro |-> [classe |-> "barbaro", hp |-> 150, tipo |-> "personagem", paralisia |-> FALSE, imunidade |-> FALSE, iniciativa |-> 0],
  Monstro |-> [classe |-> "monstro", hp |-> 100, tipo |-> "monstros", paralisia |-> FALSE, imunidade |-> FALSE, iniciativa |-> 0]
]

(* iniciativa - d20 para determinar quem começa *)
LancarD20 ==
    \E novasIniciativas \in [DOMAIN criaturas -> 1..20]:
        criaturas' = [c \in DOMAIN criaturas |-> [criaturas[c] EXCEPT !.iniciativa = novasIniciativas[c]]]

(* ordenar criaturas com base na iniciativa - usando a dica disponibilizada pela prof *)
OrdenarCriaturas ==
    LET criaturasComIniciativa == { [iniciativa |-> criaturas[c].iniciativa, id |-> c] : c \in DOMAIN criaturas }
    IN
    ordemDeAtaque' = SetToSortSeq(criaturasComIniciativa, LAMBDA r1, r2 : r1.iniciativa > r2.iniciativa)

(* dano *)
dano(criatura, dmg) ==
    IF criaturas[criatura].imunidade (*se o personagem tiver imunizado não recebe dano*)
    THEN criaturas[criatura]
    ELSE [criaturas[criatura] EXCEPT !.hp = @ - dmg]

(* ataque *)
Ataque(attacker, receiver) ==
    LET
        damageAmount == IF criaturas[attacker].tipo = "monstros" /\ round = 1
                        THEN 10
                        ELSE IF criaturas[attacker].tipo = "monstros"
                        THEN 20
                        ELSE 10
    IN
    /\ criaturas' = [criaturas EXCEPT ![receiver] = dano(receiver, damageAmount)]
    /\ ultimoAtaque' = [attacker |-> attacker, receiver |-> receiver, type |-> "ataque", damage |-> damageAmount]

(*imunidade - clerigo que dá imunidade, mas todos os personagens recebem*)
Imunidade(attacker) ==
    /\ criaturas' = [c \in DOMAIN criaturas |-> 
                        IF criaturas[c].tipo = "personagem" THEN 
                            [criaturas[c] EXCEPT !.imunidade = TRUE]
                        ELSE
                            criaturas[c]]
    /\ ultimoAtaque' = [attacker |-> attacker, type |-> "imunidade"]

(* inicialização *)
Init ==
    /\ criaturas = CRIATURAS
    /\ ultimoAtaque = [type |-> "", attacker |-> "", receiver |-> "", damage |-> 0]
    /\ ordemDeAtaque = << >>
    /\ proximo = 1         
    /\ round = 1
    /\ inicializado = FALSE


Next ==
    IF ~inicializado (* o IF e essa variavel garante que os dados só sejam lançados quando o jogo começa *)
    THEN
        /\ LancarD20
        /\ OrdenarCriaturas
        /\ proximo' = 1 
        /\ inicializado' = TRUE
        /\ UNCHANGED <<ultimoAtaque, round>>
    ELSE
        /\ OrdenarCriaturas (*aqui eu chamo OrdenarCriaturas dnv pra garantir que a OrdemAtaque esteja certa *)
        /\ LET currentAttacker == ordemDeAtaque[proximo].id
               possibleReceivers == {r \in DOMAIN criaturas : 
                                     r /= currentAttacker /\ 
                                     criaturas[r].tipo /= criaturas[currentAttacker].tipo /\ 
                                     criaturas[r].hp > 0}
           IN
            /\ criaturas[currentAttacker].hp > 0
            /\ criaturas[currentAttacker].paralisia = FALSE
            /\ \E action \in {"ataque", "imunidade"} :
               \/ (action = "ataque" /\ \E receiver \in possibleReceivers: Ataque(currentAttacker, receiver))
               \/ (criaturas[currentAttacker].classe = "clerigo" /\ action = "imunidade" /\ \E receiver \in possibleReceivers: Imunidade(currentAttacker)) (*garanto que só o clerigo possa dar imunidade*)
            /\ proximo' = IF proximo < Len(ordemDeAtaque) THEN proximo + 1 ELSE 1
            /\ round' = IF proximo' = 1 THEN round + 1 ELSE round
            /\ UNCHANGED <<inicializado>>

===============================================