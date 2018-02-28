module hospital

sig Hospital {
	medicos: set Medico,
	enfermeiros: set Enfermeiro,
	pacientes: set Paciente
}


sig Medico {
	pacientes: set Paciente
}{
	#pacientes <= 5
}

sig Enfermeiro {

}

sig  Paciente {

}

sig PacienteCirurgia extends Paciente {

}



pred show[] {}
run show for 3
