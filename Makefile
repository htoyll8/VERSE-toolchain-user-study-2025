.PHONY: init update_submodules pull_docker

init: update_submodules

update_submodules:
	git submodule update --init --recursive

pull_docker:
	docker pull bracevac/cn #TODO: point to artifactory
