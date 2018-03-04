module hospital


------------------------------------------------------------------------
-- PROJETO ALLOY: HOSPITAL

-- GRUPO: 8

--  DAVI LAERTE
--  GABRIEL FERNANDES
--  JOSÉ IVAN
--  YURI SILVA

-- CLIENTE: GABRIELA MOTTA

-- PROFESSOR: TIAGO MASSONI
-------------------------------------------------------------------------


-- ASSINATURAS

one sig Hospital {
    medicos: set Medico,
    enfermeiros: set Enfermeiro
}

sig Medico {
    cuidados: set Cuidar
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

sig Cuidar {
    paciente: one Paciente
}


-- FUNÇOES

fun temPacientesMedico[m: Medico]: set Cuidar {
    m.cuidados
}

fun procedimentoEnfermeirosAlocados[p: ProcedimentoEnfermeiro]: set Enfermeiro {
    p.~procedimentosEnfermeiro
}

fun pacienteProcedimentosAlocados[p: Paciente]: set ProcedimentoEnfermeiro {
    p.~pacienteProcedimentoEnfermeiro
}

fun pacienteEnfermeirosAlocados[p: Paciente]: set Enfermeiro {
    p.~pacienteProcedimentoEnfermeiro.~procedimentosEnfermeiro
}


-- PREDICADOS

pred todoEnfermeiroTaNoHospital[] {
    all e: Enfermeiro | one e.~enfermeiros
}

pred todoMedicoTaNoHospital[] {
    all m: Medico | one m.~medicos
}

pred temNoMaxUmMedico[p: Paciente] {
    lone p.~paciente.~cuidados
}

pred todoPacienteTemNoMaxUmMedico[] {
    all p: Paciente | temNoMaxUmMedico[p]
}

pred todoMedicoTemAteCincoPacientes[] {
    all m: Medico | #temPacientesMedico[m] <= 5
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

pred todoPacienteEhTidoNoMaxPorUmCuidar[] {
    all p: Paciente | lone p.~paciente
}

pred todoCuidarTemUmMedico[] {
    all c: Cuidar | one c.~cuidados
}

pred todoPacienteCirurgiaTemDoisProcedimentosDiferentes[] {
    all p : PacienteCirurgia, p1: PacienteCirurgia | !((p.~pacienteProcedimentoEnfermeiro in MudarSoro and p1.~pacienteProcedimentoEnfermeiro in MudarSoro) or (p.~pacienteProcedimentoEnfermeiro in MinistrarMedicamentos and p1.~pacienteProcedimentoEnfermeiro in MinistrarMedicamentos) or (p.~pacienteProcedimentoEnfermeiro in MedirPressao and p1.~pacienteProcedimentoEnfermeiro in MedirPressao))
}


-- FATOS

fact Medico {
    todoMedicoTaNoHospital[]
    todoMedicoTemAteCincoPacientes[]
}

fact Enfermeiro {
    todoEnfermeiroTemTresProcedimentos[]
    todoEnfermeiroTaNoHospital[]
}

fact Paciente {
    todoPacienteTemProcedimento[]
    todoPacienteTemEnfermeiro[]
    todoPacienteTemNoMaxUmMedico[]
    todoPacienteEhTidoNoMaxPorUmCuidar[]
    todoPacienteCirurgiaTemDoisProcedimentosDiferentes
}

fact ProcedimentoEnfermeiro {
    todoProcedimentoTemUmEnfermeiro[]
}

fact Cuidar {
    todoCuidarTemUmMedico[]
}


--TESTES

assert todoMedicoTemAteCincoPacientes {
    all m: Medico | #m.cuidados<= 5
}

assert todoEnfermeiroTemTresProcedimentos {
    all e: Enfermeiro | #e.procedimentosEnfermeiro = 3
}

assert todoPacienteTemNoMaxUmMedico {
    all p: Paciente | lone p.~paciente.~cuidados
}

assert todoPacienteNormalTemUmEnfermeiro {
    all p: PacienteNormal |  #p.~pacienteProcedimentoEnfermeiro.~procedimentosEnfermeiro = 1
}

assert todoPacienteCirurgiaTemDoisEnfermeiros {
    all p: PacienteCirurgia |  #p.~pacienteProcedimentoEnfermeiro.~procedimentosEnfermeiro = 2
}

assert todoProcedimentoTemUmEnfermeiro {
    all p: ProcedimentoEnfermeiro | one p.~procedimentosEnfermeiro
}

assert cuidadosIgualPaciente {
    #cuidados = #paciente
}


-- CRIAÇAO DO DIAGRAMA

pred show[] {}
run show for 15

check todoPacienteCirurgiaTemDoisEnfermeiros for 3
check todoPacienteNormalTemUmEnfermeiro for 3
check todoPacienteTemNoMaxUmMedico for 3
check todoMedicoTemAteCincoPacientes for 3
check todoEnfermeiroTemTresProcedimentos for 3
check todoProcedimentoTemUmEnfermeiro for 3
check cuidadosIgualPaciente for 3
