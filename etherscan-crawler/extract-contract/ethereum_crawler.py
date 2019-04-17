
# browser = webdriver.PhantomJS("D:/private-chain/first-time-crawl/phantomjs-2.1.1-windows/bin/phantomjs")
# browser = webdriver.Chrome("D:/private-chain/chromedriver")

# 判斷是有source code的網頁，還是沒有source code的網頁，再抓取opcode

from urllib.request import Request, urlopen
from bs4 import BeautifulSoup
from selenium import webdriver
from selenium.webdriver.common.keys import Keys
import win32clipboard
import win32con
import pyperclip

import time
import os
import re

import csv
import psycopg2

# 1. 爬取https://etherscan.io/accounts/c的account網址，400頁 10000個網址
# 2. 到 https://etherscan.io/address/xxxxxxxxxxxxxxxxxxxxxxx#code 抓取 source code 及 opcode



# 跳轉至opcode轉成source code頁面進行編譯
def byte_to_opcode(code):
    browser.get("https://etherscan.io/opcode-tool")
    # browser.find_element_by_id("ContentPlaceHolder1_txtByteCode").clear()
    pyper_text = pyperclip.copy(code)
    browser.find_element_by_id("ContentPlaceHolder1_txtByteCode").send_keys(Keys.CONTROL, 'v')
    # browser.find_element_by_id("ContentPlaceHolder1_txtByteCode").send_keys(code)
    browser.find_element_by_css_selector('#ContentPlaceHolder1_btnSubmit').click()
    a = browser.find_element_by_css_selector('.col-md-10').text
    c = a.index('Decoded Bytecode :')
    return a[c+20:len(a)]

# 判斷DB是否已有重複contract，沒有是0，有是1
def checkSameContract(address):
    cursor.execute("SELECT  checksame,sourcecode	FROM contract    WHERE address = '%s'" % (address) )
    rows = cursor.fetchone()
    if rows[0] == None:
        sc = rows[1].replace("'","''")
        cursor.execute("SELECT  MAX(checksame)	FROM  contract    WHERE sourcecode = '%s'" % (sc))
        sc_check = cursor.fetchone()
        if sc_check[0]  == None:
            cursor.execute("UPDATE contract SET checksame = 0 WHERE address = %s" % ("'"+i.text+"'"))
            conn.commit()
        if sc_check[0]  == 0:
            cursor.execute("UPDATE contract SET checksame = 1 WHERE address = %s" % ("'"+i.text+"'"))
            conn.commit()


dbaddress = ""
dbopcode = ""
dbsourcecode = ""
dbtxcount = 0
dbeth_balance = ""
dbeth_US_value = ""
analysisresult=""

txflag = 4

try:
    conn = psycopg2.connect(database='soslab', user='soslab',password='$0$1ab', host='140.119.19.77', port= "65432")
    # conn = psycopg2.connect(database='test', user='postgres',password='soslab', host='localhost', port= "5432")
    cursor = conn.cursor()

    for k in range(47,473):
      b = webdriver.Chrome("D:/private-chain/chromedriver")
      url = 'https://etherscan.io/contractsVerified/' + str(k)
      type(url)
      # html = Request( url, headers={'User-Agent': 'Mozilla/5.0'})
      b.get(url)

      time.sleep(6)
      webpage = b.page_source
      bsObj = BeautifulSoup(webpage, "lxml")
      a_tag = bsObj.table.findAll("a", href=True  )

      b.close()
      # 需要安裝PhantomJS，找到他的path
      browser = webdriver.Chrome("D:/private-chain/chromedriver")
      # browser = webdriver.PhantomJS("/usr/local/bin/phantomjs")
      j = 0
      s=0
      for i in a_tag:
        address_website = "https://etherscan.io/address/" + i.get_text() +"#code"
        dbtxcount = bsObj.table.findAll("td")[txflag].string
        print("第",j,"個網址",address_website)
        try:
            browser.get(address_website)
            # browser.get("https://etherscan.io/address/0xab7c74abc0c4d48d1bdad5dcb26153fc8780f83e#code")
            if j == 0:
                time.sleep(10)
            else:
                time.sleep(3)

            print("browser",browser)

            #檢查資料庫是否已有address
            cursor.execute("SELECT address FROM contract WHERE address = %s" % ("'"+i.text+"'"))
            row = cursor.fetchone()
            eth = browser.find_elements_by_xpath("//div[@class='col-md-6']/table/tbody/tr");
            dbeth_balance = eth[0].text
            dbeth_US_value = eth[1].text
            print('dbeth_balance',dbeth_balance)
            print('dbeth_US_value',dbeth_US_value)
            print(row)

            #有的話update txcount、eth_balance、eth_US_value
            if row:
                print("update db")
                checkSameContract(i.text)
                print('---ss----')
                cursor.execute("UPDATE contract SET txcount = %s, eth_balance = %s, eth_us_value =%s WHERE address = %s",(dbtxcount,dbeth_balance, dbeth_US_value, i.text) )
                print('---zz----')
                conn.commit()
                txflag += 5


            # 沒有的話insert進資料庫
            else:
                print("insert in db")

                # source code
                if browser.find_elements_by_css_selector('.btn-u.btn-u-default.btn-u-xs.js-sourcecopybtn'):
                    browser.find_element_by_css_selector('.btn-u.btn-u-default.btn-u-xs.js-sourcecopybtn').click()
                    print("有Source code")
                    win32clipboard.OpenClipboard()
                    dbsourcecode = win32clipboard.GetClipboardData()
                    win32clipboard.CloseClipboard()
                    print("**********5**********")

                    time.sleep(0.5)
                    # alert = browser.switch_to.alert.accept()
                else:
                    dbsourcecode = ""
                    print("沒有Source code")

                # opcode
                opcode = ""
                if browser.find_elements_by_css_selector('.ace_content'):
                    byte_code = browser.find_element_by_id("verifiedbytecode2").text
                    opcode = byte_to_opcode(byte_code)
                    print("**********6**********")
                else:
                    byte_code = browser.find_element_by_class_name("wordwrap").text
                    opcode = byte_to_opcode(byte_code)
                    print("**********7**********")


                dbaddress = i.get_text()
                print("**********8**********")
                print('dbaddress',dbaddress)
                # print('opcode',opcode)
                # print('dbsourcecode',dbsourcecode)
                print('analysisresult',analysisresult)
                print('dbtxcount',dbtxcount)
                print('dbeth_balance',dbeth_balance)
                print('dbeth_US_value',dbeth_US_value)
                cursor.execute("INSERT INTO CONTRACT(ADDRESS,OPCODE,SOURCECODE,ANALYSIS_RESULT,TXCOUNT,ETH_BALANCE,ETH_US_VALUE) VALUES(%s,%s,%s,%s,%s,%s,%s)",(dbaddress,opcode,dbsourcecode,analysisresult,dbtxcount,dbeth_balance,dbeth_US_value))
                print("**********9**********")
                conn.commit()
                print("**********10**********")
                checkSameContract(i.text)
                print("**********11**********")
                txflag += 5
        except Exception as ex:
            print("No opcode/sourcecoe page")
            print(ex)
        if (j == 24 ):
            browser.close()
            txflag = 4

        print("\n","第", k ,"頁 ","- 第", j,"個", "---------------------\n")
        j = j + 1

except Exception as ex:
    print("not Connected")
    print("Error: " , str(ex) )
