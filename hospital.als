module hospital


sig Medico {
	pacientesMedico: set Paciente
}{
	#pacientesMedico <= 5
}

sig Enfermeiro {
	pacientesEnfermeiro: set Paciente
}{
	#pacientesEnfermeiro = 3
}

abstract sig  Paciente {}

sig PacienteNormal extends Paciente {
}

sig PacienteCirurgia extends Paciente {
}

fun enfermeirosAlocados[p:Paciente]: set Enfermeiro {
	p.~pacientesEnfermeiro
}

fact {
  all p: PacienteNormal | #enfermeirosAlocados[p] = 1
  all p: PacienteCirurgia | #enfermeirosAlocados[p] = 2 
}


pred show[] {}
run show for 5
