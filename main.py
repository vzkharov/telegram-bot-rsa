# -*- coding: utf-8 -*-
"""
Created on Fri Mar 16 14:46:32 2022

@author: zakharovvadzim
"""
import time
import numpy as np
import math
import random as rd

import telegram
from telegram.ext.updater import Updater
from telegram.update import Update
from telegram.ext.callbackcontext import CallbackContext
from telegram.ext.commandhandler import CommandHandler
from telegram.ext.messagehandler import MessageHandler
from telegram.ext.filters import Filters

np.random.seed(100)


# Utils

def test_time(funcs, *args):
    start = time.time()

    results = []
    for func in funcs:
        results.append(func(*args))

    end = time.time()

    return results, round(end - start, 5)


def prime_to(n, min, max):
    r = rd.randint(min, max)
    gcd = math.gcd(r, n)

    while gcd != 1:
        r = rd.randint(min, max)
        gcd = math.gcd(r, n)

    return r


# Exponentiation Modulo

def mon_exp(a, b, N):
    u, v = 1, a
    b_2str = np.binary_repr(b)
    l = len(b_2str)

    for i in range(0, l):
        if b_2str[l - i - 1] != '0':
            u = (u * v) % N
        v = (v * v) % N

    return u


# Extended GCD (RSA is using 'extended_gcd_by_cycle' cause its efficiency)

GCD_ARRAY_SIZE = 2 ** 20

r_ = [0] * GCD_ARRAY_SIZE
q_ = [0] * GCD_ARRAY_SIZE
x_ = [0] * GCD_ARRAY_SIZE
y_ = [0] * GCD_ARRAY_SIZE


def extended_gcd_by_cycle(a, b):
    r_[0], r_[1] = a, b
    x_[0], x_[1] = [1, 0]
    y_[0], y_[1] = [0, 1]
    i = 1

    while r_[i] != 0:
        i += 1
        q_[i] = math.floor(r_[i - 2] / r_[i - 1])
        r_[i] = r_[i - 2] - q_[i] * r_[i - 1]
        x_[i] = x_[i - 2] - q_[i] * x_[i - 1]
        y_[i] = y_[i - 2] - q_[i] * y_[i - 1]

    return r_[i - 1], x_[i - 1], y_[i - 1]


def extended_gcd_recursion(a, b):
    if a == 0:
        return b, 0, 1

    gcd, x1, y1 = extended_gcd_recursion(b % a, a)

    x = y1 - (b // a) * x1
    y = x1

    return gcd, x, y


# Find inverse modulo

def inverse_modulo(a, m):
    _, x, _ = extended_gcd_by_cycle(a, m)
    return x % m


# Generate n-bit random numbers and test prime (miller-rabin and fermat)

def is_prime_fermat_test(fermat_candidate):
    for i in range(2, fermat_candidate):
        if math.gcd(fermat_candidate, i) != 1:
            return False
        if mon_exp(i, fermat_candidate - 1, fermat_candidate) != 1:
            return False
    return True


def is_prime_miller_rabin_test(miller_rabin_candidate):
    maxDivisionsByTwo = 0
    evenComponent = miller_rabin_candidate - 1

    while evenComponent % 2 == 0:
        evenComponent >>= 1
        maxDivisionsByTwo += 1
    assert (2 ** maxDivisionsByTwo * evenComponent == miller_rabin_candidate - 1)

    def trial_composite(r_t):
        if pow(r_t, evenComponent,
               miller_rabin_candidate) == 1:
            return False
        for j in range(maxDivisionsByTwo):
            if pow(r_t, 2 ** j * evenComponent, miller_rabin_candidate) == miller_rabin_candidate - 1:
                return False
        return True

    numberOfRabinTrials = 100
    for i in range(numberOfRabinTrials):
        round_tester = rd.randrange(2, miller_rabin_candidate)
        if trial_composite(round_tester):
            return False
    return True


def n_bit_random(n):
    return rd.randrange(2 ** (n - 1) + 1, 2 ** n - 1)


def get_n_bit_prime(n):
    while True:
        prime_candidate = n_bit_random(n)
        if is_prime_miller_rabin_test(prime_candidate):
            return prime_candidate
        else:
            continue


# RSA

def carmichael(p, q):
    return math.lcm(p - 1, q - 1)


def euler(p, q):
    return (p - 1) * (q - 1)


class RSA:
    def __init__(self):
        self.public = None
        self.private = None
        self.N = None

    def is_keys_generate(self):
        return self.public is not None and self.private is not None and self.N is not None

    def generate_keys(self, n, ftype="euler"):
        p, q = get_n_bit_prime(n), get_n_bit_prime(n)
        N = p * q

        val = euler(p, q)

        if ftype == "euler":
            val = euler(p, q)
        elif ftype == "carmichael":
            val = carmichael(p, q)

        e = prime_to(val, min=2 ** 10, max=val)
        d = inverse_modulo(e, val)

        self.public = e
        self.private = d
        self.N = N

        return e, N

    def encrypt(self, m, publicKey):
        return mon_exp(m, publicKey, self.N)

    def decrypt(self, c):
        return mon_exp(c, self.private, self.N)


# Test Functions

def test_rsa(n):
    rsa = RSA()

    def test_rsa_by_ftype(n, ftype="euler"):
        print('[!!!] FTYPE:', ftype)

        # generate keys

        _, time_gen = test_time([rsa.generate_keys], n, ftype)
        print('rsa.generate_keys (s):', time_gen)

        e, N = _[0]

        # generate random data to encrypt

        data = n_bit_random(n)

        # encrypt

        _, time_enc = test_time([rsa.encrypt], data, e)
        print('rsa.encrypt (s):', time_enc)
        c = _[0]

        # decrypt

        _, time_dec = test_time([rsa.decrypt], c)
        print('rsa.decrypt (s):', time_dec)
        m = _[0]

        return (data % N) == m

    return test_rsa_by_ftype(n, "carmichael")


def test_extended_gcd(n):
    a, b = get_n_bit_prime(n), get_n_bit_prime(n)
    _, time_gcd = test_time([extended_gcd_by_cycle], a, b)
    gcd, x, y = _[0]
    return gcd == math.gcd(a, b), time_gcd


def test_inverse_modulo(n):
    m = n_bit_random(n)
    a = prime_to(m, min=2 ** 10, max=m)
    _, time_inv = test_time([inverse_modulo], a, m)
    result = _[0]
    return (a * result) % m == 1, time_inv


def test_mon_exp(n):
    a, b = n_bit_random(n), n_bit_random(n)
    N = n_bit_random(2 * n)
    _, time_mon_exp = test_time([mon_exp], a, b, N)
    result = _[0]
    return result == pow(a, b, N), time_mon_exp


# Telegram Bot

def __bot__():
    rsa = RSA()

    print('Telegram Bot is running...')

    updater = Updater("5280187600:AAHAXw6iev8zh3PXgyn7u_9j1xYrrKr07p8")

    def start(update, context):
        dot_unicode = u'\u00b7'
        hello_msg = " Тестирование алгоритмов RSA"
        author_msg = "Автор бота: Лемнёв Вадим"
        ps_msg = "_P.S. при генерации ключей рекомендую выбирать n <= 512_\n" + dot_unicode + " _n = 1024_, затраченное время _~ 8 секунд_\n" + dot_unicode + " _n = 2048_, затраченное время _~ 60 секунд_\n"
        output = "\n".join([hello_msg, author_msg, ps_msg])
        update.message.reply_text(output, parse_mode=telegram.ParseMode.MARKDOWN)

    def service(update, context):
        gen_help = "/gen {_n_} - генерирует пару ключей и выводит на экран _N = pq_ и _publicKey_"
        enc_help = "/enc {_publicKey_} {_data_} - шифрует _data_ по _publicKey_ и выводит на экран результат"
        dec_help = "/dec {_data_} - расшифровывает _data_ и выводит результат на экран"
        output = "\n".join([gen_help, enc_help, dec_help])
        update.message.reply_text(output, parse_mode=telegram.ParseMode.MARKDOWN)

    def gen(update, context):
        if len(context.args) < 1:
            update.message.reply_text("Не все аргументы указаны")
            return

        n = int(context.args[0])
        public, N = rsa.generate_keys(n)

        output = str(public)
        update.message.reply_text(output, parse_mode=telegram.ParseMode.MARKDOWN)

    def enc(update, context):
        if len(context.args) < 2:
            update.message.reply_text("Не все аргументы указаны")
            return

        publickey = int(context.args[0])
        m = int(context.args[1])

        is_keys_exists = rsa.is_keys_generate()

        if not is_keys_exists:
            update.message.reply_text("Сначала сгенерируйте ключи")
            return

        c = rsa.encrypt(m, publickey)
        output = str(c)
        update.message.reply_text(output, parse_mode=telegram.ParseMode.MARKDOWN)

    def dec(update, context):
        if len(context.args) < 1:
            update.message.reply_text("Не все аргументы указаны")
            return

        c = int(context.args[0])

        is_keys_exists = rsa.is_keys_generate()

        if not is_keys_exists:
            update.message.reply_text("Сначала сгенерируйте ключи")
            return

        m = rsa.decrypt(c)
        output = str(m)
        update.message.reply_text(output, parse_mode=telegram.ParseMode.MARKDOWN)

    updater.dispatcher.add_handler(CommandHandler('start', start))
    updater.dispatcher.add_handler(CommandHandler('help', service))
    updater.dispatcher.add_handler(CommandHandler('gen', gen))
    updater.dispatcher.add_handler(CommandHandler('enc', enc))
    updater.dispatcher.add_handler(CommandHandler('dec', dec))

    updater.start_polling()
    updater.idle()


# Entrypoint

__bot__()
