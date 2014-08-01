DIR=$(dirname $0)
CMD="DYLD_LIBRARY_PATH=$DIR/lib:$DYLD_LIBRARY_PATH exec $DIR/bin/rustc $@"
# echo $CMD
eval "$CMD"
