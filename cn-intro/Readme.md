# CN Examples directory 

To get CN to watch some file for modifications and rerun the 

```console
  echo "tutorial.c" | entr -c ../cn/cn --slow-smt=1 --state-file=./tutorial.html tutorial.c
```

This relies on the `entr` utility which monitors files for changes. 
