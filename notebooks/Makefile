
fatberry-jupyter-server:
	#SYMPY_USE_CACHE=no PYTHONPATH=../src/:../../../programming-contests/competitive-programming/python-libs/ jupyter-notebook --no-browser --port=5901 --ip=150.217.37.116
	PYTHONPATH=../src/:../../../programming-contests/competitive-programming/python-libs/ jupyter-notebook --no-browser --port=5901 --ip=150.217.37.116

thinkpad-jupyter-server:
	#use SYMPY_USE_CACHE=no to not use caching in SymPy computation; however, this produces some errors, for example in series expansions, so for now we leave it commented.
	PYTHONPATH=../src/:/home/mn/Developer/working-copies/programming-contests/competitive-programming/python-libs/ jupyter-notebook --no-browser --port=5901

tex-convert:
	jupyter-nbconvert --to latex --output tex-generated/fibonacci-numbers-unary-indexed-unfolding.tex fibonacci-numbers-unary-indexed-unfolding.ipynb 
