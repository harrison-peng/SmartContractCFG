class Generator:
    def __init__(self):
        self.count_data = 0
        self.count_gas = 0
        self.count_var = 0
        self.count_addr = 0
        self.count_storage = 0
        self.count_mem = 0
        self.count_balance = 0
        self.count_exp = 0

    def gen_data_var(self):
        self.count_data += 1
        return 'Id_%s' % self.count_data

    def gen_data_size(self):
        return 'Id_size'

    def gen_mem_var(self):
        self.count_mem += 1
        return 'mem_%s' % self.count_mem

    def gen_arbitrary_var(self):
        self.count_var += 1
        return 'var_%s' % self.count_var

    def gen_arbitrary_address_var(self):
        self.count_addr += 1
        return 'address_%s' % self.count_addr

    def gen_owner_store_var(self):
        self.count_storage += 1
        return 'storage_%s' % self.count_storage

    def gen_gas_var(self):
        self.count_gas += 1
        return 'gas_%s' % self.count_gas

    def gen_gas_price_var(self):
        return 'Ip'

    def gen_exp_var(self):
        return 'Iexp_%s' % self.count_exp

    def gen_caller_var(self):
        return 'Is'

    def gen_value_var(self):
        return 'Iv'

    def gen_origin_var(self):
        return 'Io'

    def gen_balance_var(self):
        self.count_balance += 1
        return 'balance_%s' % self.count_balance

    def gen_code_var(self, address, position, bytecount):
        return 'code_%s_%s_%s' % (address, position, bytecount)

    def gen_code_size_var(self, address):
        return 'code_size_%s' % address


class SolverUnsatCore:
    def __init__(self):
        self.count = 0

    def set_count(self, number):
        self.count = number

    def get_count(self):
        return self.count

    def get_pc_var(self):
        self.count += 1
        return 'pc_%s' % self.count
