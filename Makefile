.PHONY: check check-dry-run blind inventory controls audit index index-check
check:
	python3 scripts/check.py
check-dry-run:
	python3 scripts/check.py --dry-run
blind:
	python3 scripts/blind.py --jobs 4
inventory:
	python3 scripts/inventory.py

controls:
	python3 scripts/negative-controls.py

audit:
	python3 scripts/audit.py

index:
	python3 scripts/index.py
index-check:
	python3 scripts/index.py --check
