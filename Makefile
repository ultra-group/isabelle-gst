build-html: 
	isabelle build -D "src" -P "html" -v GST
build-heap:
	isabelle build -D "src" -vbR