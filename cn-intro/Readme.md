# CN Examples directory 

To get CN to watch a file for modifications and rerun the verification tool on changes, you can call the shell script as follows:

```console
  ./run_cn.sh tutorial.c
```

This relies on the `entr` utility which monitors files for changes. 
