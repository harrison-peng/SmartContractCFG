contract SimpleStorage {
    uint storedData;
    function add(uint x, uint y) {
        for (uint i = 0; i < x; i++) {
            if (x == y) {
                storedData += y;
            }
        }
    }
    function set(uint x) {
        storedData = x;
    }
    function get() constant returns (uint retVal) {
        return storedData;
    }
}
