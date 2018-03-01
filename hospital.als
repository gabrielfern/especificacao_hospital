module hospital


sig Enfermeiro {
	pacientes: set PacienteNormal
}{
	#pacientes = 3
}

abstract sig  Paciente {

}

sig PacienteNormal extends Paciente {

}

sig PacienteCirurgia extends Paciente {

}

fact {
  all e: Enfermeiro |  some e.~pacientes
}




pred show[] {}
run show for 8
