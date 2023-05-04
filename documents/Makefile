all : intro_slides.pdf

PSFILES=bezier_example.ps bezier_example2.ps cells_spiral.ps \
  collision.ps collision2.ps empty_spiral.ps polygon.ps repair2.ps \
  repair.ps smooth_spiral.ps smooth_spiral2.ps spiral_bline.ps spiral_safe2.ps\
  partial_spiral.ps partial_spiral2.ps

PDFFILES= $(PSFILES:.ps=.pdf)

intro_slides.pdf : intro_slides.tex $(PDFFILES)
	pdflatex intro_slides.tex

$(PDFFILES): %.pdf: %.ps
	ps2pdf $<
