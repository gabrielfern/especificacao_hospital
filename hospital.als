module hospital


sig Medico {
	pacientes: set Paciente
}{
	#pacientes <= 5
}

sig Enfermeiro {
	pacientesNormal: set PacienteNormal,
	pacientesCirurgia: set PacienteCirurgia
}{
	#(pacientesNormal + pacientesCirurgia) = 3
}

abstract sig  Paciente {

}

sig PacienteNormal extends Paciente {

}

sig PacienteCirurgia extends Paciente {

}

fact {
  all p: PacienteNormal | one p.~pacientesNormal
  all p: PacienteCirurgia | #p.~pacientesCirurgia = 2
}




pred show[] {}
run show for 5
