-------------- MODULE batalha --------------
EXTENDS Integers, Sequences, SequencesExt, TLC

VARIABLES criaturas, proximo, round, ordemDeAtaque, ultimoAtaque, inicializado

CONSTANTS Mago, Clerigo, Barbaro, Monstro

CRIATURAS == [
  Mago    |-> [classe |-> "mago", hp |-> 20, tipo |-> "personagem", paralisia |-> "nenhuma", imunidade |-> FALSE, provocacao |-> "nenhuma", iniciativa |-> 0],
  Clerigo |-> [classe |-> "clerigo", hp |-> 20, tipo |-> "personagem", paralisia |-> "nenhuma", imunidade |-> FALSE, provocacao |-> "nenhuma", iniciativa |-> 0],
  Barbaro |-> [classe |-> "barbaro", hp |-> 150, tipo |-> "personagem", paralisia |-> "nenhuma", imunidade |-> FALSE, provocacao |-> "nenhuma", iniciativa |-> 0],
  Monstro |-> [classe |-> "monstro", hp |-> 100, tipo |-> "monstros", paralisia |-> "nenhuma", imunidade |-> FALSE, provocacao |-> "nenhuma", iniciativa |-> 0]
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
    THEN [criaturas[criatura] EXCEPT !.hp = @ - (dmg * 0)]
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
    /\ criaturas[attacker].tipo /= criaturas[receiver].tipo
    /\ (criaturas[attacker].tipo = "monstros" /\ criaturas[attacker].provocacao = "provocado") => criaturas[receiver].classe = "barbaro"
    /\ criaturas' = [c \in DOMAIN criaturas |-> 
                     IF c = receiver
                     THEN dano(c, damageAmount)  (* primeiro aplica o dano *)
                     ELSE IF criaturas[attacker].classe = "clerigo" /\ criaturas[c].tipo = "personagem"
                     THEN [criaturas[c] EXCEPT !.imunidade = FALSE]  (* imunidade eh removida pois nesse turno clerigo decidiu atacar *)
                     ELSE IF criaturas[attacker].tipo = "monstros" /\ criaturas[attacker].provocacao = "provocado" (*atualizo a provocacao *)
                     THEN [criaturas[c] EXCEPT !.provocacao = "nenhuma"]
                     ELSE criaturas[c]] 
    /\ ultimoAtaque' = [attacker |-> attacker, receiver |-> receiver, type |-> "ataque", damage |-> damageAmount]

(*imunidade - clerigo que dá imunidade, mas todos os personagens recebem*)
Imunidade(attacker) ==
    /\ criaturas' = [c \in DOMAIN criaturas |-> 
                        IF criaturas[c].tipo = "personagem" THEN 
                            [criaturas[c] EXCEPT !.imunidade = TRUE]
                        ELSE
                            criaturas[c]]
    /\ ultimoAtaque' = [attacker |-> attacker, type |-> "imunidade"]

Paralisar(attacker, receiver) ==
    /\ criaturas[attacker].tipo /= criaturas[receiver].tipo  (* personagem nao paralisa personagem*)
    /\ criaturas' = [criaturas EXCEPT ![receiver] = 
                     IF criaturas[attacker].tipo = "monstros"
                     THEN [criaturas[receiver] EXCEPT !.paralisia = "permanente"]
                     ELSE [criaturas[receiver] EXCEPT !.paralisia = "temporaria"]]
    /\ ultimoAtaque' = [attacker |-> attacker, receiver |-> receiver, type |-> "paralisia"]

Provocar(attacker, receiver) ==
    /\ criaturas[attacker].tipo /= criaturas[receiver].tipo  
    /\ criaturas[attacker].classe = "barbaro"
    /\ criaturas[receiver].tipo = "monstros"
    /\ criaturas' = [criaturas EXCEPT ![receiver] = [criaturas[receiver] EXCEPT !.provocacao = "provocado"]]
    /\ ultimoAtaque' = [attacker |-> attacker, receiver |-> receiver, type |-> "provocacao"]

(*ajudar paralisado - personagens ajudam personagens*)
Ajudar(attacker, receiver) ==
    /\ criaturas[attacker].tipo = "personagem"
    /\ criaturas[receiver].tipo = "personagem"
    /\ criaturas[receiver].paralisia /= "nenhuma"
    /\ criaturas' = [c \in DOMAIN criaturas |-> 
                     IF c = receiver
                     THEN [criaturas[c] EXCEPT !.paralisia = "nenhuma"]  (* remove a paralisia primeiro *)
                     ELSE IF criaturas[attacker].classe = "clerigo" /\ criaturas[c].tipo = "personagem"
                     THEN [criaturas[c] EXCEPT !.imunidade = FALSE]  (* se for o clerigo quem tiver ajudando, remove a imunidade *)
                     ELSE criaturas[c]]
    /\ ultimoAtaque' = [attacker |-> attacker, receiver |-> receiver, type |-> "ajuda"]

atualizarParalisia ==
    criaturas' = [c \in DOMAIN criaturas |-> 
                  IF criaturas[c].paralisia = "temporaria"
                  THEN [criaturas[c] EXCEPT !.paralisia = "nenhuma"]
                  ELSE criaturas[c]]

atualizarProvocacao ==
    criaturas' = [c \in DOMAIN criaturas |-> 
                  IF criaturas[c].provocacao = "provocado"
                  THEN [criaturas[c] EXCEPT !.provocacao = "nenhuma"]
                  ELSE criaturas[c]]

(* inicialização *)
Init ==
    /\ criaturas = CRIATURAS
    /\ ordemDeAtaque = << >>
    /\ ultimoAtaque = [type |-> "", attacker |-> "", receiver |-> "", damage |-> 0, status |-> ""]
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
        /\ OrdenarCriaturas (*aqui eu chamo OrdenarCriaturas dnv pra garantir que a OrdemAtaque esteja certa - preciso verificar o pq q isso acontece *)
        /\ \A c \in DOMAIN criaturas : criaturas[c].hp > 0  (* se alguma criatura tiver morrido, não vai para o proximo round *)
        /\ LET currentAttacker == ordemDeAtaque[proximo].id
               possibleReceivers == {r \in DOMAIN criaturas : 
                                     r /= currentAttacker /\ 
                                     criaturas[r].hp > 0}
           IN
            /\ criaturas[currentAttacker].hp > 0
            /\  IF criaturas[currentAttacker].paralisia = "temporaria" 
                    THEN
                        /\ atualizarParalisia
                        /\ ultimoAtaque' = [type |-> "", attacker |-> "", receiver |-> "", damage |-> 0, status |-> "monstro nao realizou acao pois estava paralisado"]
                ELSE IF criaturas[currentAttacker].paralisia = "nenhuma"
                THEN 
                    /\ \E action \in {"ataque", "imunidade", "paralisar", "ajudar", "provocar"} :
                        \/ (action = "ataque" /\ \E receiver \in possibleReceivers: Ataque(currentAttacker, receiver))
                        \/ (criaturas[currentAttacker].classe = "mago" /\ action = "paralisar" /\ \E receiver \in possibleReceivers: Paralisar(currentAttacker, receiver))
                        \/ (criaturas[currentAttacker].classe = "monstro" /\ criaturas[currentAttacker].provocacao = "nenhuma" /\ action = "paralisar" /\ \E receiver \in possibleReceivers: Paralisar(currentAttacker, receiver))
                        \/ (criaturas[currentAttacker].tipo = "personagem" /\ action = "ajudar" /\ \E receiver \in possibleReceivers: Ajudar(currentAttacker, receiver))              
                        \/ (criaturas[currentAttacker].classe = "barbaro" /\ action = "provocar" /\ \E receiver \in possibleReceivers: Provocar(currentAttacker, receiver))
                        \/ (criaturas[currentAttacker].classe = "clerigo" /\ action = "imunidade" /\ \E receiver \in possibleReceivers: Imunidade(currentAttacker))       
                ELSE (* preciso melhorar a atualizacao do ultimo ataque - ta feio mas pelo menos ta falando q foi imunizado ao inves de repetir o ataque anterior *)
                    /\ ultimoAtaque' = [type |-> "", attacker |-> "", receiver |-> "", damage |-> 0, status |-> "personagem nao realizou acao pois esta paralisado"]
                    /\ UNCHANGED <<criaturas>>
            /\ proximo' = IF proximo < Len(ordemDeAtaque) THEN proximo + 1 ELSE 1
            /\ round' = IF proximo' = 1 THEN round + 1 ELSE round
            /\ UNCHANGED <<inicializado>>

(* invariantes *)
MonstroNaoMorre == criaturas["Monstro"].hp > 0

NenhumPersonagemMorre == /\ criaturas["Mago"].hp > 0
                         /\ criaturas["Clerigo"].hp > 0
                         /\ criaturas["Barbaro"].hp > 0

===============================================
