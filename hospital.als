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

one sig Hospital {
	medicos: set Medico,
	enfermeiros: set Enfermeiro
}

sig Medico {
	medicoPacientes: set MedicoPaciente
}
sig MedicoPaciente {
	medicoPaciente: one Paciente
}
sig Enfermeiro {
	procedimentosEnfermeiro: set ProcedimentoEnfermeiro    
}

abstract sig Paciente {}

sig PacienteNormal extends Paciente {}

sig PacienteCirurgia extends Paciente {}

abstract sig ProcedimentoEnfermeiro {
	pacienteProcedimentoEnfermeiro: one Paciente
}

sig MedirPressao extends ProcedimentoEnfermeiro {}

sig MinistrarMedicamentos extends ProcedimentoEnfermeiro {}

sig MudarSoro extends ProcedimentoEnfermeiro {}

-- FUNÇOES

fun procedimentoEnfermeirosAlocados[p: ProcedimentoEnfermeiro]: set Enfermeiro {
	p.~procedimentosEnfermeiro
}

fun pacienteProcedimentosAlocados[p: Paciente]: set ProcedimentoEnfermeiro {
	p.~pacienteProcedimentoEnfermeiro
}

fun pacienteEnfermeirosAlocados[p: Paciente]: set Enfermeiro {
	p.~pacienteProcedimentoEnfermeiro.~procedimentosEnfermeiro
}

fun temPacientesMedico[m: Medico]: set MedicoPaciente {
	m.medicoPacientes
}

-- PREDICADOS

pred temNoMaxUmMedico[p: Paciente] {
	lone p.~medicoPaciente.~medicoPacientes
}

pred todoPacienteTemNoMaxUmMedico[] {
	all p: Paciente | temNoMaxUmMedico[p]
}

pred todoMedicoTemAteCincoPacientes[] {
	all m: Medico | #temPacientesMedico[m] <= 5
}

pred todoPacienteEhTidoNoMaxPorUmMedicoPaciente[] {
	all p: Paciente | lone p.~medicoPaciente
}

pred todoMedicoPacienteTemUmMedico[] {
	all mp: MedicoPaciente | one mp.~medicoPacientes
}

pred todoEnfermeiroTemTresProcedimentos[] {
	all e: Enfermeiro | #e.procedimentosEnfermeiro = 3
}

pred todoProcedimentoTemUmEnfermeiro[] {
	all p: ProcedimentoEnfermeiro | one procedimentoEnfermeirosAlocados[p]
}

pred todoPacienteTemProcedimento[] {
	all p: PacienteNormal | #pacienteProcedimentosAlocados[p] = 1
	all p: PacienteCirurgia | #pacienteProcedimentosAlocados[p] = 2  
}

pred todoPacienteTemEnfermeiro[] {
	all p: PacienteNormal | #pacienteEnfermeirosAlocados[p] = 1
	all p: PacienteCirurgia | #pacienteEnfermeirosAlocados[p] = 2
}

pred todoEnfermeiroTaNoHospital[] {
	all e: Enfermeiro | one e.~enfermeiros
}

pred todoMedicoTaNoHospital[] {
	all m: Medico | one m.~medicos
}

-- FATOS
fact Medico {
	todoMedicoTaNoHospital[]
     todoPacienteTemNoMaxUmMedico[]
     todoMedicoTemAteCincoPacientes[]
	todoMedicoPacienteTemUmMedico[]
}

fact Enfermeiro {
	todoEnfermeiroTemTresProcedimentos[]
	todoEnfermeiroTaNoHospital[]
}

fact ProcedimentoEnfermeiro {
	todoProcedimentoTemUmEnfermeiro[]
}

fact Paciente {
	todoPacienteEhTidoNoMaxPorUmMedicoPaciente[]
	todoPacienteTemProcedimento[]
	todoPacienteTemEnfermeiro[]
}

--TESTES

assert todoPacienteTemNoMaxUmMedico {
    all p: Paciente | lone p.~medicoPaciente.~medicoPacientes
}

assert todoPacienteNormalTemUmEnfermeiro {
    all p: PacienteNormal |  #p.~pacienteProcedimentoEnfermeiro.~procedimentosEnfermeiro = 1
}

assert todoPacienteCirurgiaTemDoisEnfermeiros {
    all p: PacienteCirurgia |  #p.~pacienteProcedimentoEnfermeiro.~procedimentosEnfermeiro = 2
}

assert todoMedicoTemAteCincoPacientes {
    all m: Medico | #m.medicoPacientes <= 5
}

assert todoEnfermeiroTemTresProcedimentos {
    all e: Enfermeiro | #e.procedimentosEnfermeiro = 3
}

assert todoProcedimentoTemUmEnfermeiro {
    all p: ProcedimentoEnfermeiro | one p.~procedimentosEnfermeiro
}

assert medicoPacientesIgualMecidoPaciente {
	#medicoPacientes = #medicoPaciente
}

-- CRIAÇAO DO DIAGRAMA

pred show[] {}
run show for 4

check todoPacienteCirurgiaTemDoisEnfermeiros for 3
check todoPacienteNormalTemUmEnfermeiro for 3
check todoPacienteTemNoMaxUmMedico for 3
check todoMedicoTemAteCincoPacientes for 3
check todoEnfermeiroTemTresProcedimentos for 3
check todoProcedimentoTemUmEnfermeiro for 3
