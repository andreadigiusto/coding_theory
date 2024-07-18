readfile := function(N)
    s := Read(N);
    OB := eval s;
    return OB;
end function;

//PrintFileMagma("namefile.m" , print_obj : Overwrite:=true); prints file WITH overwrite