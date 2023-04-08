# ETH-DANCE 技术文档

## 1.简介

为了更加方便地对合约进行部署测试，我们做了ETH-DANCE这个项目，创造了一门与合约交互的新的编程语言，具有以下独有的功能特性：
* 强类型语言，但在编写过程中可以有更简易的类型转换
* 可以读取abi，检查合约类型，发送合约测试结果，并可以非常简洁地切换账户发送合约

## 2.基本语法

* 每行语句用 **`=`** 进行赋值，例如```count = 0```
* **`:`** 表示调用合约，例如```counter_factory = :deploy(CounterFactory)```
* **`.`** 表示调用方法，例如``` counter = counter_factory.getresult()```

## 3.数据类型

### 3.1 number类型
* 没有特殊记号的情形下，默认是uint类型
* 数字后面加f表示浮点数类型(未实现)，例如 ```num0 = 1.2f```, ```num1 = 1.2f8```
* 数字后面加q表示定点数类型，默认是64位，例如 `1.2 * 1<<10`
- ```num0 = 1.2q``` result: ```vm: "num0" = [int256] 13333333333333333 == 1.2 * 1<<64```
- ```num1 = 1.2q10``` result: ```vm: "num1" = [int256] 4cd == 1.2 * 1<<10```
* 数字后面加d表示Digital类型，默认是18位，例如 * 1e18
- ```num0 = 1.2d``` result: ```vm: "num0" = [int256] 10a741a462780000 == 1.2e18```
- ```num1 = 1.2d10``` result: ```vm: "num1" = [int256] 2cb417800 == 1.2e10```

### 3.2 string类型
* 没有特殊记号的情形下，默认是长度为256的string
* 可以在string前加上prefix 代表 encoding
* 前缀**key**表示密钥private key类型，例如 ```account = key"0x0f5fc8fb1d77aa3e06cc0c91c0e00fc588b1f959eccdd563b0c2dbf3e32a12aa"```
* 前缀**hex**表示是16进制编码的bytes类型，例如 ```str1 = hex"8fb1d77aa3e06cc0c91c0e00fc50"```
* 前缀**address**表示address类型，例如 ```addr1 = address"0xf39Fd6e51aad88F6F4ce6aB8827279cffFb92266"```

### 3.3 contract类型
* 读取合约abi的json文件后，自动识别合约类型及参数，
* 如果调用不存在的合约或者参数类型不匹配，会显示编译错误停止执行

### 3.4 主动类型标记（annotation）
* 对于一些返回值为Address的函数，可以主动标记返回类型为某个contract，例如`counter: Counter = counter_factory.get_counter()`

### 3.5 内置变量
* 内置变量改变虚拟机的状态，会影响之后执行的所有合约
* `$account`表示接下来的transaction用哪个账户（目前只支持private key）
* `$endpoint`, `$gas`, `$confirm_interval`等内部变量也会在未来支持实现

## 6.TODO
* float类型实现
* 接收合约发出transaction的结果
