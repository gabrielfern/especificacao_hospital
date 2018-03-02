module hospital


sig Medico {
	pacientesMedico: set Paciente
}{
	#pacientesMedico <= 5
}

sig Enfermeiro {
	pacientesEnfermeiro: set Paciente
}

abstract sig  Paciente {}

sig PacienteNormal extends Paciente {
}

sig PacienteCirurgia extends Paciente {
}

fun enfermeirosAlocados[p:Paciente]: set Enfermeiro {
	p.~pacientesEnfermeiro
}

pred temTresPacientes[e: Enfermeiro] {
	#e.pacientesEnfermeiro = 3
}

fact {
  all p: PacienteNormal | #enfermeirosAlocados[p] = 1
  all p: PacienteCirurgia | #enfermeirosAlocados[p] = 2
  all e: Enfermeiro | temTresPacientes[e]
}

assert todoPacienteTemEnfermeiro {
	all p:Paciente | some p.~pacientesEnfermeiro
}


pred show[] {}
run show for 5
check todoPacienteTemEnfermeiro for 5
