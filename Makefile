
all: hata

meta:
	cd Buildsystem/MetaBuilder && stack install

hata: meta
	metabuild hata


