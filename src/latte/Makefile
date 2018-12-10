
MARKDOWNIZE_PATH = ../../../markdownize
PYTHON = python3

MARKDOWNIZE = $(PYTHON) $(MARKDOWNIZE_PATH)/markdownize.py

MFLAGS = --begin ";;{" --end ";;}" --lang "clojure" --remove-prefix-re ";;[ \t]*"

OBJS = core.clj.md

all: markdownize

markdownize: $(OBJS)

%.clj.md : %.clj
	$(MARKDOWNIZE) --input $< --output $@ $(MFLAGS)

clean:
	rm -f *~
	rm -f *.md



