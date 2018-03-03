module hospital


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

fun enfermeirosAlocados[p: Paciente]: set Enfermeiro {
	p.~pacientesEnfermeiro
}

fun temPacientesEnfermeiro[e: Enfermeiro]: set Paciente {
	e.pacientesEnfermeiro
}

fun temPacientesMedico[m: Medico]: set Paciente {
	m.pacientesMedico
}

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

fact {
  todoPacienteTemEnfermeiro[]
  todoEnfermeiroTemTresPacientes[]
  todoPacienteTemNoMaxUmMedico[]
  todoMedicoTemAteCincoPacientes[]
}

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

pred show[] {}
run show for 5
check todoPacienteCirurgiaTemDoisEnfermeiros for 3
check todoPacienteNormalTemUmEnfermeiro for 3
check todoPacienteTemNoMaxUmMedico for 3
check todoMedicoTemAteCincoPacientes for 3
check todoEnfermeiroTemTresPacientes for 3
