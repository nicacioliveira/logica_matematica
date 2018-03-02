module contratacao_de_funcionarios

-------------------------------------------------------------------- assinaturas ----------------------------------------------------
--CONTRATO
one sig JornadaDeTrabalho{}
abstract sig Contrato{
	jornada : JornadaDeTrabalho
}
one sig PrazoDeterminado, PrazoIndeterminado extends Contrato{}

--FUNCAO OBRIGATORIA
some sig Funcao{}

-- ATIVIDADES
abstract sig Atividade{}

abstract sig AtividadePrazoDeterminado		extends Atividade{}
lone sig AtendimentoDeClientes 		extends AtividadePrazoDeterminado{}
lone sig SetorDeMarketing 			extends AtividadePrazoDeterminado{}
lone sig ServicosGerais 				extends AtividadePrazoDeterminado{}

abstract sig AtividadePrazoIndeterminado 		extends Atividade{}
lone sig AuxiliarDeContratos 			extends AtividadePrazoIndeterminado{}
lone sig EquipeAdministativa 			extends AtividadePrazoIndeterminado{}
lone sig AuxiliarDeJovemAprendiz 		extends AtividadePrazoIndeterminado{}


abstract sig Funcionario {
	funcao : one Funcao,
	contrato : one Contrato,
	atividades : set Atividade
}

------------------------------------------------------------------ predicados -------------------------------------------------------

//limite de atividades por usuario
pred limite_atividades[f : Funcionario] {
	#get_atividades_funcionario[f] <= 3 and #get_atividades_funcionario[f] >= 1
}

//contrato nao pode ser de dois tipos
pred contrato_tipo[f : Funcionario] {
	(f.contrato in PrazoDeterminado and f.contrato !in PrazoIndeterminado) or (f.contrato in PrazoIndeterminado and f.contrato !in PrazoDeterminado) 
}

//tipo de atividade para tipo de contrato
pred atividade_por_contrato[f : Funcionario] {
	(f.contrato = PrazoDeterminado implies f.atividades in AtividadePrazoDeterminado ) and
	(f.contrato = PrazoIndeterminado implies f.atividades in AtividadePrazoIndeterminado)
}

pred atividade_de_um_funcionario[f : Funcionario, a : Atividade] {
	a in f.atividades
}

pred funcao_por_funcionario[f : Funcao] {
	some f.~funcao
}
----------------------------------------------------------------- fatos ------------------------------------------------------------------

fact {
	all f : Funcao | funcao_por_funcionario[f]
}

fact {
	all f : Funcionario | limite_atividades[f]
}

fact {
	all f : Funcionario | contrato_tipo[f]
}

fact {
	all f : Funcionario | atividade_por_contrato[f]
}

fact {
	all a : Atividade | one f : Funcionario | atividade_de_um_funcionario[f, a]
}


----------------------------------------------------------------- testes ----------------------------------------------------------------

assert tipoDeAtividadePorContrato {
	all f : Funcionario | get_atividades_funcionario[f] in AtividadePrazoDeterminado implies get_contrato_funcionario[f] = PrazoDeterminado
	all f : Funcionario | get_atividades_funcionario[f] in AtividadePrazoIndeterminado implies get_contrato_funcionario[f] = PrazoIndeterminado
}

assert funcaoObrigatoria {
	all f : Funcionario | one f.funcao
}

assert umContrato {
	all f : Funcionario | one f.contrato
}

assert qtd_atividades {
	all f : Funcionario | #get_atividades_funcionario[f] >= 1 and #get_atividades_funcionario[f] <= 3
}

----------------------------------------------------------------- funcoes -------------------------------------------------------------
fun get_atividades_funcionario[f : Funcionario]: set Atividade {
	f.atividades
}

fun get_funcionarios_atividades[a : Atividade]: set Funcionario {
	a.~atividades
}

fun get_contrato_funcionario[f : Funcionario]: Contrato {
	f.contrato
}

----------------------------------------------------------------- check's --------------------------------------------------------------
check tipoDeAtividadePorContrato
check funcaoObrigatoria
check umContrato
check qtd_atividades


----------------------------------------------------------------- run ---------------------------------------------------------------------
pred show[]{}
run show for 10
