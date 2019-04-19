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
        self.count_log = 0
        self.count_time = 0
        self.count_loop = 0

    def gen_data_var(self, line):
        return 'Id_%s' % line

    def gen_data_size(self, line):
        return 'Id_size'

    def gen_code_var(self, line):
        return 'Ic_%s' % line

    def gen_mem_var(self, line):
        self.count_mem += 1
        return 'mem_%s' % line

    def gen_arbitrary_var(self, line):
        self.count_var += 1
        return 'var_%s' % line

    def gen_arbitrary_address_var(self, line):
        self.count_addr += 1
        return 'address_%s' % line

    def gen_owner_store_var(self, line):
        self.count_storage += 1
        return 'storage_%s' % line

    def gen_gas_var(self, line):
        self.count_gas += 1
        return 'gas_%s' % line

    def gen_gas_price_var(self, line):
        return 'Ip_%s' % line

    def gen_exp_var(self, line):
        return 'Iexp_%s' % line

    def gen_caller_var(self, line):
        return 'Ia_caller'

    def gen_value_var(self, line):
        return 'Iv'

    def gen_origin_var(self, line):
        return 'Io_%s' % line

    def gen_balance_var(self, line):
        self.count_balance += 1
        return 'balance_%s' % line

    # def gen_code_var(self, address, position, bytecount, line):
    #     return 'code_%s_%s_%s_%s' % (address, position, bytecount, line)

    def gen_code_size_var(self, address, line):
        return 'code_size_%s' % line

    def gen_log_var(self, line):
        self.count_log += 1
        return 'log_%s' % line

    def gen_time_var(self, line):
        self.count_time += 1
        return 'It_%s' % line

    def gen_hash_var(self, num, line):
        if isinstance(num, int):
            return 'Ih_%s_%s' % (num, line)
        else:
            return 'Ih_%s' % line

    def gen_loop_var(self):
        self.count_loop += 1
        return 'loop_%s' % self.count_loop

    def gen_sha_var(self, line):
        # return 'sha3(%s)_%s' % (val, line)
        return 'Isha3_%s' % line


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
