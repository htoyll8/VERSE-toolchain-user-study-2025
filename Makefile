.PHONY: init update_submodules pull_docker

init: update_submodules pull_docker

update_submodules:
	git submodule update --init --recursive

pull_docker:
	docker pull artifactory.galois.com:5032/cn 
