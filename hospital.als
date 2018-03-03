module hospital

------------------------------------------------------------------------
-- PROJETO ALLOY: HOSPITAL

-- GRUPO: 8

--	DAVI LAERTE
--	GABRIEL FERNANDES
--	JOSÉ IVAN
--	YURI SILVA

-- CLIENTE: GABRIELA MOTTA

-- PROFESSOR: TIAGO MASSONI

-------------------------------------------------------------------------

-- ASSINATURAS

sig Medico {
	pacientesMedico: set Paciente
}
sig Enfermeiro {
	pacientesEnfermeiro: set Paciente
}

abstract sig  Paciente {}

sig PacienteNormal extends Paciente {
}

sig PacienteCirurgia extends Paciente {
}

abstract sig ProcedimentoMedico {}

sig ProcedimentoTratarDoenca extends ProcedimentoMedico {}

sig ProcedimentoRealizarCirugia extends ProcedimentoMedico {}

abstract sig ProcedimentoEnfermeiro {}

sig ProcedimentoMedirPressao extends ProcedimentoEnfermeiro {}

sig ProcedimentoMinistrarMedicamentos extends ProcedimentoEnfermeiro {}

sig ProcedimentoMudarSoro extends ProcedimentoEnfermeiro {}

-- FUNÇOES

fun enfermeirosAlocados[p: Paciente]: set Enfermeiro {
	p.~pacientesEnfermeiro
}

fun temPacientesEnfermeiro[e: Enfermeiro]: set Paciente {
	e.pacientesEnfermeiro
}

fun temPacientesMedico[m: Medico]: set Paciente {
	m.pacientesMedico
}

-- PREDICADOS

pred temNoMaxUmMedico[p: Paciente] {
	lone p.~pacientesMedico
}

pred todoPacienteTemEnfermeiro[] {
  all p: PacienteNormal | #enfermeirosAlocados[p] = 1
  all p: PacienteCirurgia | #enfermeirosAlocados[p] = 2
}

pred todoEnfermeiroTemTresPacientes[] {
  all e: Enfermeiro | #temPacientesEnfermeiro[e] = 3
}

pred todoPacienteTemNoMaxUmMedico[] {
  all p: Paciente | temNoMaxUmMedico[p]
}

pred todoMedicoTemAteCincoPacientes[] {
  all m: Medico | #temPacientesMedico[m] <= 5
}

-- FATOS

fact {
  todoPacienteTemEnfermeiro[]
  todoEnfermeiroTemTresPacientes[]
  todoPacienteTemNoMaxUmMedico[]
  todoMedicoTemAteCincoPacientes[]
}

--TESTES

assert todoPacienteTemNoMaxUmMedico {
	all p: Paciente | lone p.~pacientesMedico
}

assert todoPacienteNormalTemUmEnfermeiro {
	all p: PacienteNormal |  #p.~pacientesEnfermeiro = 1
}

assert todoPacienteCirurgiaTemDoisEnfermeiros {
	all p: PacienteCirurgia |  #p.~pacientesEnfermeiro = 2
}

assert todoMedicoTemAteCincoPacientes {
	all m: Medico | #m.pacientesMedico <= 5
}

assert todoEnfermeiroTemTresPacientes {
	all e: Enfermeiro | #e.pacientesEnfermeiro = 3
}

-- CRIAÇAO DO DIAGRAMA

pred show[] {}
run show for 5

check todoPacienteCirurgiaTemDoisEnfermeiros for 3
check todoPacienteNormalTemUmEnfermeiro for 3
check todoPacienteTemNoMaxUmMedico for 3
check todoMedicoTemAteCincoPacientes for 3
check todoEnfermeiroTemTresPacientes for 3
