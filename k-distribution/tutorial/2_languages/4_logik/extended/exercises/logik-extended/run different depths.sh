
kompile --backend java logik.k;

for i in {1..15}; do 
krun --search-final tests/list-member-1.logik --depth $i; 
echo "=========================================================================="
done

