default: string.vo playground.vo

%.vo: %.v
	coqc $<

string.vo: char.vo
