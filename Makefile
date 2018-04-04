all : vmd.vo seot_util.vo analysis.vo

analysis.vo: analysis.v
	coqc analysis.v

seot_util.vo : seot_util.v
	coqc seot_util.v

vmd.vo : vmd.v seot_util.vo analysis.vo
	coqc vmd.v

clean :
	rm *.vo *.glob
