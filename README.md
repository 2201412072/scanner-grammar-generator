该项目分为两部分，一个是词法分析器生成器，一个是语法分析器生成器。
词法分析器：它通过将nfa转为dfa，从而达到线性的解析速度。
自动转换自动机.cpp：它是主要代码，需要提供一个定义nfa的文件作为输入，然后程序解析并输出能够处理该nfa的程序。
自动机程序_LR.txt：它是上面定义nfa文件的例子。
自动机程序_LR_array.txt：它是程序解析过程中生成的配置文件，不能删除，否则后续生成的程序无法工作。
自动机程序_LR_dfa.txt：它是生成的程序，它通过“自动机程序_array.txt”来运行工作。

该程序输入一个nfa文件A.txt后，会生成A_array.txt以及A_dfa.txt。


语法分析器：它通过解析cfg得到SLR语法分析器。
LR0或1生成器.cpp：它是主要代码，需要提供一个定义cfg文件作为输入。
cfg_LR.txt：定义cfg文件的例子1
cfg1.txt：定义cfg文件例子2
cfg_LR_detail.txt：它是代码处理过程中生成的中间状态，可以用于查看中间过程是否正确，可以删掉。
cfg_LR_slr_array.txt：它是程序解析过程中生成的配置文件，不能删除，否则后续生成的程序无法工作。
cfg_LR_slr_procedure.txt：它是生成的程序，它通过“cfg_LR_slr_array.txt”来运行工作

该程序输入一个cfg文件A.txt后，会生成A_array.txt以及A_procedure.txt。
