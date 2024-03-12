dot_in := scheduling
dot_out := $(patsubst %,%.png,$(dot_in))

.PHONY : all
all : dot

.PHONY : dot
dot : $(dot_out)

%.png : %.dot
	@ dot -Gdpi=200 -Tpng -o $*.png $<

.PHONY : clean
clean :
	@ rm -f $(dot_out)
